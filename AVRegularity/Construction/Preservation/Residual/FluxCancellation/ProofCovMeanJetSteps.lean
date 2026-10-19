-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanLeftReindex
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredConstantsWindow
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Proofs.Results.Construction.SuccWindowData.Jacobian
import AVenhance.Infra.Construction.StreamAdmissible

section
section
/-! **Source mean, Right: the vocabulary and the three steps.**

`SourceMeanRightStatement` reads `ℓ ∘ (Q_p 𝐄^flux P_p g)_j` as the path side. The steps:

* `RightPulseReadStatement` (the Hilbert-lift path sum on the native chain of one odd pulse with a nonzero cutoff,
  and the identification of the Eulerian pulse flux with the push-forward of the path mean): for
  every grade `r` and degree `n`, `ℓ` of the pulse term of `P_p g` is the sum over the paths into
  `v` of the pushed path mean of `ℓ ∘ C_π ∘ (P_p g)`;
* `RightPathRegStatement` (the regularity lemma on the path family): the pushed path mean of a
  smooth field is `C^{2p}` in the Eulerian variable;
* `RightPathLinearStatement` (finite order form / recentring): the pushed path mean is linear on
  smooth fields, so it commutes with the expansion `P_p φ = ∑ 𝒞^{a'} φ / a'!`.

The glue (finite sums, `ℓ` and the components commuting with `Q_p`, the dressed terms) is part of
the proof of `sourceMeanRight`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The scalar field of the path `π`: `ℓ ∘ C_π ∘ g_{src π}`. -/
def rightField {G : GenStage D hr Dm b j₀} (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) {h : ℕ} (π : StagePath G h)
    (hπ : π.src ∈ G.comps) : Vec 2 → ℝ :=
  fun y => ℓ (rootPathMap hr π.src.root π.mapList v.1.root (g y ⟨π.src, hπ⟩))

/-- The path mean of the pulse `k` pushed to the Eulerian variables by the natural chart. -/
def pathJ (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (k : ℤ)
    (t : ℝ) (φ : Vec 2 → ℝ) : Vec 2 → Vec 2 :=
  pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
    (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t)
    (nativePathMean Mn G π Cc n k t) φ

/-- **The pulse-reading step**: the Hilbert-lift path sum read through the pulse term. -/
def RightPulseReadStatement : Prop :=
  HilbertLiftPathSumStatement →
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT → ∀ (W : SplitWitness P Mn G G')
      (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) →
    ∀ (v : CompIn G.comps) (t : ℝ) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2)
      (k : ℤ) (hk : Odd k), ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
    ∀ r ∈ Finset.Icc 1 depth, ∀ n ∈ Finset.Icc 2 (Mn.N + Dm), ∀ y : Vec 2,
      ℓ (pulseMeanFluxEuler (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
        (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
          (Mn.lenFactor * liftLength D G.level)) n r
        (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k)
        (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
        (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s')
        (menuCovPRep Mn D G.level Mn.p (fun _ => g)) t y v j) =
      ∑ᶠ π : StagePath G r, if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
        pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
          (fun z => ℓ (rootPathMap hr π.src.root π.mapList v.1.root
            (menuCovPRep Mn D G.level Mn.p (fun _ => g) t z ⟨π.src, hπ.2⟩))) y j
      else 0

/-- **The regularity step**: the pushed path mean of a smooth field is `C^{2p}`. -/
def RightPathRegStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT → ∀ (W : SplitWitness P Mn G G') (t : ℝ)
      (k : ℤ), Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
    ∀ r ∈ Finset.Icc 1 depth, ∀ n ∈ Finset.Icc 2 (Mn.N + Dm), ∀ π : StagePath G r,
    ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      ContDiff ℝ ((2 * Mn.p : ℕ) : WithTop ℕ∞)
        (pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t φ)

/-- **The linearity step**: the pushed path mean is linear on smooth fields (it commutes with the expansion
`P_p φ = ∑_{a' ≤ p} 𝒞^{a'} φ / a'!`). -/
def RightPathLinearStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT → ∀ (W : SplitWitness P Mn G G') (t : ℝ)
      (k : ℤ), Odd k → ocCutoff D.α D.q D.Λ G.level k t ≠ 0 →
    ∀ r ∈ Finset.Icc 1 depth, ∀ n ∈ Finset.Icc 2 (Mn.N + Dm), ∀ π : StagePath G r,
    ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → ∀ y : Vec 2,
      pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
        (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p φ) y =
      ∑ a' ∈ Finset.range (Mn.p + 1), ((a'.factorial : ℝ)⁻¹) •
        pathJ Mn G π (W.Cc (SuccSource.copyQuad [] r π)) n k t
          ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) y

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Proof of `RootSourceBookkeepingStatement`: parents, words, weights and provenance of the
identities of the successor out of the roots, from the source bijection `e` of
`IsActualSuccessor`, `compParent_eq_self`, `parent_word_succComp`, `stagePath_src_mem` and
`stagePath_tgt_mem`, and `Real.rpow_add`. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The old source of a valid source is a component of the incoming stage. -/
theorem rsb_oldSrc_mem {G : GenStage D hr Dm b j₀} {A : Finset WordLetter} {J : ℕ}
    (s : SuccSource G) (hs : s.Valid A J) : s.oldSrc ∈ G.comps := by
  have h3 := hs.2.2
  cases s with
  | copyDir t v u γ => exact u.2
  | copyQuad t h π => exact Providers.CascadeInvariants.stagePath_src_mem π h3
  | letterDiag t u => exact u.2
  | letterMean t n h π => exact Providers.CascadeInvariants.stagePath_src_mem π h3
  | letterCov t n h a a' π => exact Providers.CascadeInvariants.stagePath_src_mem π h3

/-- The old target of a valid source is a component of the incoming stage. -/
theorem rsb_oldTgt_mem {G : GenStage D hr Dm b j₀} {A : Finset WordLetter} {J : ℕ}
    (s : SuccSource G) (hs : s.Valid A J) : s.oldTgt ∈ G.comps := by
  have h3 := hs.2.2
  cases s with
  | copyDir t v u γ => exact v.2
  | copyQuad t h π => exact Providers.CascadeInvariants.stagePath_tgt_mem π h3
  | letterDiag t u => exact u.2
  | letterMean t n h π => exact Providers.CascadeInvariants.stagePath_tgt_mem π h3
  | letterCov t n h a a' π => exact Providers.CascadeInvariants.stagePath_tgt_mem π h3

/-- A source whose source component is an old component has the empty word. -/
theorem rsb_word_nil {G : GenStage D hr Dm b j₀} {m : ℕ} (hm : 1 ≤ m) (s : SuccSource G)
    {u : Comp} (hu : ∀ e ∈ u.births, m ≤ e.scale) (h : s.srcComp m = u) : s.word = [] := by
  by_contra hw
  have h' : succComp m s.oldSrc s.word = u := h
  have hb := hu ⟨m - 1, s.word, hw⟩ (by
    rw [← h']
    simp [succComp, hw])
  simp at hb
  omega

/-- The source is the first source exactly when its provenance is `letter m diag []`. -/
theorem rsb_isDiag_iff {G : GenStage D hr Dm b j₀} (m : ℕ) (s : SuccSource G) :
    s.IsDiag ↔ s.prov m = Prov.letter m WordLetter.diag [] := by
  cases s <;> simp [SuccSource.IsDiag, SuccSource.prov, Prov.letter.injEq]

/-- The readout weight of a row cancels the normalization of the source, for a source with the
empty word. -/
theorem rsb_weight {G : GenStage D hr Dm b j₀} (m : ℕ) (η₀ : ℝ) (hE : 0 < D.eps (m - 1))
    (s : SuccSource G) (hw : s.word = []) :
    D.eps (m - 1) ^ (η₀ * ((s.newWord.length : ℕ) : ℝ)) * SuccSource.lam m η₀ s = 1 := by
  unfold SuccSource.newWord SuccSource.lam
  rcases hl : s.letter? with _ | l
  · simp [hw]
  · simp only [hw, List.nil_append, List.length_singleton, Nat.cast_one, mul_one]
    rw [← Real.rpow_add hE]
    simp

/-- (The root-bookkeeping step) Bookkeeping of the identities of the successor out of the roots. -/
theorem rootSourceBookkeeping : RootSourceBookkeepingStatement := by
  classical
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' hin hact W
  have hm : 1 ≤ G.level := hact.1
  have hcomps : G'.comps = succExtComps G.level Mn.A Mn.J G.comps := hact.2.2.1
  have hold := hin.old_births
  have hε : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hin.base
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    have h := InitialValue.compParent_eq_self hm (hold c hc)
    exact ⟨by rw [hcomps]; exact Finset.mem_union_left _ hc, h.1, h.2⟩
  · intro v' u' γ' hu
    obtain ⟨hval, hsrc, htgt⟩ := (W.e v' u' γ').2
    have hw : (W.e v' u' γ').1.word = [] := rsb_word_nil hm _ (hold _ hu) hsrc
    have hsrc' : (W.e v' u' γ').1.oldSrc = u'.1 := by
      have h : succComp G.level (W.e v' u' γ').1.oldSrc (W.e v' u' γ').1.word = u'.1 := hsrc
      rw [hw] at h
      simpa [succComp] using h
    have hT := rsb_oldTgt_mem _ hval
    have hpw := Preservation.FullLift.parent_word_succComp hm (W.e v' u' γ').1.oldTgt
      (hold _ hT) (W.e v' u' γ').1.newWord
    have ht' : succComp G.level (W.e v' u' γ').1.oldTgt (W.e v' u' γ').1.newWord = v'.1 := htgt
    rw [ht'] at hpw
    refine ⟨hw, hsrc', hT, hpw.1, hpw.2, ?_, ?_⟩
    · rw [hpw.2]
      exact rsb_weight G.level Mn.η0 hε _ hw
    · rw [(W.spec v' u' γ').1]
      exact rsb_isDiag_iff G.level _
  · intro s hs hw
    have hS := rsb_oldSrc_mem s hs
    have hT := rsb_oldTgt_mem s hs
    have hsrcEq : s.srcComp G.level = s.oldSrc := by
      simp [SuccSource.srcComp, hw, succComp]
    have hmemS : s.srcComp G.level ∈ G'.comps := by
      rw [hcomps, hsrcEq]; exact Finset.mem_union_left _ hS
    have hmemT : s.tgtComp G.level ∈ G'.comps := by
      rw [hcomps]
      unfold SuccSource.tgtComp succExtComps
      by_cases hn : s.newWord = []
      · rw [Finset.mem_union]
        left
        simpa [succComp, hn] using hT
      · rw [Finset.mem_union]
        right
        rw [Finset.mem_image]
        refine ⟨(s.oldTgt, s.newWord), Finset.mem_product.2 ⟨hT, ?_⟩, rfl⟩
        have hl : ∃ l, s.letter? = some l := by
          unfold SuccSource.newWord at hn
          rcases hl : s.letter? with _ | l
          · simp [hl, hw] at hn
          · exact ⟨l, rfl⟩
        obtain ⟨l, hl⟩ := hl
        have hlA := hs.2.1 l hl
        have hnw : s.newWord = [l] := by simp [SuccSource.newWord, hl, hw]
        rw [hnw]
        simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc]
        refine ⟨1, ⟨le_rfl, by omega⟩, ?_⟩
        simp only [wordsOfLength, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
        exact ⟨(l, []), ⟨hlA.2, rfl⟩, rfl⟩
    refine ⟨⟨s.tgtComp G.level, hmemT⟩, ⟨s.srcComp G.level, hmemS⟩,
      (W.e ⟨s.tgtComp G.level, hmemT⟩ ⟨s.srcComp G.level, hmemS⟩).symm ⟨s, hs, rfl, rfl⟩, ?_, ?_⟩
    · simp
    · show s.srcComp G.level ∈ G.comps
      rw [hsrcEq]; exact hS

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Grade zero of the Hilbert lift path sum**: `HilbertLiftGradeZeroStatement`.

The diagonal candidate `δ_{vu} C0 · id` is a grade-zero lift sequence of the Hilbert operator data
(`hlDiag_isLiftSequence`); the Hilbert lift `CcT` is a lift sequence of the same data; the lift
sequence is unique on the window (`lift_sequence_unique_window`), so `CcT` and the candidate agree
at grade zero; and the slow flux of the candidate along `ℓ` is the scalar flux of the
scalarization (`hl_fluxMean_transfer`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity AVenhance
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- The pulse drift of a family lift is smooth in the fast variable. -/
theorem hl_familyLiftData_drift_smooth {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (D : OCData) (m : ℕ)
    (k : ℤ) (A : RealChain) (ρ : ℝ) (edge : ConstituentEdges Dm h) (t : ℝ) (c : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => (familyLiftData D m k A ρ edge).v t z c) := by
  have hs := EntryWeakProofs.ocShearVel_spatial_smooth D.α D.q D.Λ m k
  have hv : ContDiff ℝ (⊤ : ℕ∞) (ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) k t) := by
    unfold ocPulseCellDrift
    exact ((hs.comp (contDiff_id.const_smul (ocEpsilon D.q D.Λ m))).const_smul
      (ocPulse D.α D.q D.Λ D.ζ m k (ocEll D.q D.Λ m (D.kap m) ^ 2 * t))).const_smul
      (ocEll D.q D.Λ m (D.kap m) ^ 2 / ocEpsilon D.q D.Λ m)
  exact contDiff_pi.mp hv c

/-- Restricting a lift sequence to grade zero. -/
theorem hl_isLiftSequence_grade_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Dm : ℕ} {Q : LiftOperatorData ι h Dm} {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) :
    IsLiftSequence Q sX sZ t₀ t₁ N 0 Cc := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  exact ⟨h0, fun hh hl hH => h1 hh hl (hH.trans (Nat.zero_le _)),
    fun hh hH => h2 hh (hH.trans (Nat.zero_le _)),
    fun hh hH => h3 hh (hH.trans (Nat.zero_le _)),
    fun hh hH => h4 hh (hH.trans (Nat.zero_le _)),
    fun hh hH => h5 hh (hH.trans (Nat.zero_le _)),
    fun hh hH => h6 hh (hH.trans (Nat.zero_le _))⟩

/-- **Step 1 of the path-sum step: grade zero.** -/
theorem hilbertLiftGradeZero : HilbertLiftGradeZeroStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G hin hsX hsZ ρ hρ depth CcT k hk hadm hlift τ hτ a ha n X
    hX j v ℓ C0 hC0
  classical
  have hζ := hin.profile
  have hab : D.slotStart G.level k / D.cellScaleSq G.level ≤
      (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level :=
    hτ.1.trans hτ.2
  have hN1 := hin.cutoff
  set edge := G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩) with hedge
  let Q := familyLiftData D G.level k (nativeChain G.level k) ρ edge
  let Q0 := familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k
    (nativeChain G.level k) ρ (fun _ _ _ => [])
  have hη : Q0.η = Q.η := rfl
  have hG : Q0.G = Q.G := rfl
  have hv' : Q0.v = Q.v := rfl
  have hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j) := fun t i j =>
    EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k (nativeChain G.level k) rfl ρ
      edge t i j
  have hvs : ∀ t c, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z c) := fun t c =>
    hl_familyLiftData_drift_smooth D G.level k (nativeChain G.level k) ρ edge t c
  have hCd := hlDiag_isLiftSequence (hs := fun v : CompIn G.comps => hr v.1.root) C0 Q Q0 hη hG hv' hC0
    hab (by omega) (by omega) (by omega) hGs hvs
  have hH := hl_isLiftSequence_grade_zero hlift
  have hW : ∀ X', ∃ lo A Mv : ℝ, AVRegularity.Uniqueness.WindowData
      (fun t => Matrix.of (Q.G t X')) Q.v (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) lo A Mv := by
    intro X'
    obtain ⟨lo, hi, hlo, he⟩ := Providers.GenSem.familyLiftData_pos_window D hζ G.level k
      (nativeChain G.level k) ρ edge _ _ X'
    obtain ⟨Mv, hMv⟩ := Providers.GenSem.familyLiftData_v_bounded D hζ G.level hk
      (nativeChain G.level k) ρ edge
    exact ⟨lo, hi, Mv, AVRegularity.Uniqueness.windowData_of_elliptic
      (fun t => Matrix.of (Q.G t X')) Q.v _ _ lo hi Mv
      (fun t => Providers.GenSem.familyLiftData_symm D G.level k (nativeChain G.level k) ρ edge t X' 0 1)
      hlo he (fun t _ z => hMv t z)⟩
  have huniq := AVRegularity.Uniqueness.lift_sequence_unique_window Q _ _ hab hW Mn.sX Mn.sZ Mn.N 0
    (CcT k) (hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) C0) hH hCd
  have hF : ∀ n', liftApply n' (CcT k 0 n') a τ =
      liftApply n' (hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) C0 0 n') a τ := by
    intro n'
    refine AVRegularity.Uniqueness.liftApply_congr (fun m _ α => ?_) rfl
    funext X' z' v' u'
    exact huniq 0 le_rfl n' m α τ hτ X' z' v' u'
  have hflux : liftFluxX Q (CcT k) a 0 n τ =
      liftFluxX Q (hlDiagCoeff (fun v : CompIn G.comps => hr v.1.root) C0) a 0 n τ := by
    funext X' z' k'
    rw [liftFluxX_zero_formula, liftFluxX_zero_formula, hF (n - 1), hF (n - 2)]
  have hbox := fun n' m α v' u' => (hCd.2.2.2.2.2.1 0 le_rfl n' m α v' u' τ hτ).1
  have hbox0 := fun n' m α v' u' => (hC0.2.2.2.2.2.1 0 le_rfl n' m α v' u' τ hτ).1
  have := hl_fluxMean_transfer (hs := fun v : CompIn G.comps => hr v.1.root) C0 Q Q0 hη hG hv' ℓ
    a n τ X j (fun i i' => (hGs τ i i').of_le (by exact_mod_cast le_top))
    (fun c => (hvs τ c).of_le (by exact_mod_cast le_top))
    ((ha τ).of_le (by exact_mod_cast le_top))
    (fun n' m α v' u' => (hbox n' m α v' u').mono (by omega) (by omega))
    (fun n' m α v' u' => (hbox0 n' m α v' u').mono (by omega) (by omega))
  rw [hflux]
  exact this

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Proof of `PiecePiolaFiniteOrderStatement`: the finite-smoothness flux identity
`transportedCoeff_flux_orders_of_contDiff` at `n = Dγ - 1`, where
`Dγ ≤ (Dγ - 1) + 1` holds for every `Dγ`. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- (The Piola-transport step) The Piola transport of one chart piece at finite order. -/
theorem piecePiolaFiniteOrder : PiecePiolaFiniteOrderStatement := by
  intro E _ _ χ ψ hχ hψ hψχ hχψ Dγ V hV B x a₀
  exact AVRegularity.CycleComparison.Reconstruction.transportedCoeff_flux_orders_of_contDiff
    hχ hψ hψχ hχψ hV Dγ (by omega) B x a₀

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Spatial regularity of the glued mean flux `menuGluedMeanFlux`.

For a stage `G` with the split input, the glued mean flux over the pulses, grades `rs ⊆ [0, depth]` and
any degrees `ns` is `C^s` in space, when the coarse field is `C^{s+Dm+N}` and `s + Dm ≤ sX, sZ`. The edge
coefficients of `G` enter only for a positive grade (the source flux), through the hypothesis
`ActualFluxJointSmooth G` (the conclusion of `native_actual_flux_joint_contDiff`). -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The cell drift of a pulse is smooth in the fast variable. -/
theorem ocPulseCellDrift_contDiff (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) {k : ℤ}
    (hk : Odd k) (s : ℝ) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ocPulseCellDrift α q Λ ζ m ν k s z j) := by
  unfold ocPulseCellDrift
  simp only [Pi.smul_apply, smul_eq_mul]
  exact contDiff_const.mul (contDiff_const.mul
    ((AVRegularity.CycleWords.ocShearVel_component_contDiff (α := α) (q := q) (Λ := Λ) (m := m)
      hk j).comp (contDiff_const_smul _)))

/-- At a time where the cutoff of the slot `k` does not vanish, the pulse clock lies in the lift window. -/
theorem clock_mem_window (D : OCData) (m : ℕ) (k : ℤ) (t : ℝ)
    (hτ : 0 < ocTau D.α D.q D.Λ m) (hc : 0 < D.cellScaleSq m)
    (hcut : ocCutoff D.α D.q D.Λ m k t ≠ 0) :
    (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
  have hw := AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  obtain ⟨h1, h2⟩ := hw
  rw [inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right h1 hc.le, div_le_div_of_nonneg_right h2 hc.le⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- Box smoothness of the lifted fiber edges of a pulse at the pulse clock. -/
theorem fiber_edge_boxSmooth (G : GenStage D hr Dm b j₀) (hE : ActualFluxJointSmooth G)
    (k : ℤ) (hk : Odd k) (A : RealChain) (ρ t : ℝ) (hc : D.cellScaleSq G.level ≠ 0)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) (s : ℕ) :
    ∀ v u d, ∀ γ ∈ (familyLiftData D G.level k A ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))).edge v u d,
      ∀ α, IsBoxSmooth s s (fun X z => γ.coeff α ((D.cellScaleSq G.level)⁻¹ * t) X z) := by
  intro v u d γ hγ α
  refine AVRegularity.Construction.Preservation.FullLift.liftEdges_boxSmooth_of_joint
    (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1))
    (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)) s s {(D.cellScaleSq G.level)⁻¹ * t} {t} ?_ ?_
    v u d γ hγ α _ rfl
  · intro t' ht'
    rw [Set.mem_singleton_iff] at ht' ⊢
    rw [ht', ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · intro v u d γ hγ α t' ht'
    rw [Set.mem_singleton_iff] at ht'
    subst ht'
    simp only [ChartedFamily.fiber, List.mem_filterMap] at hγ
    obtain ⟨γ₁, _, hγ₁⟩ := hγ
    split_ifs at hγ₁ with hd
    cases hγ₁
    exact hE ⟨k, hk⟩ v u γ₁ d.1 α t' ht _

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **The glued mean flux is `C^s` in space.** -/
theorem menuGluedMeanFlux_contDiff (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ)
    (rs ns : Finset ℕ) (hrs : ∀ r ∈ rs, r ≤ depth)
    (hE : (∃ r ∈ rs, r ≠ 0) → ActualFluxJointSmooth G)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a t)) (v : CompIn G.comps) :
    ContDiff ℝ (s : ℕ∞) (fun x => menuGluedMeanFlux Mn G G.level rs ns CcT a t x v) := by
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  unfold menuGluedMeanFlux
  refine ContDiff.sum fun k _ => ContDiff.sum fun r hr => ContDiff.sum fun n _ => ?_
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
    · simp only [hcut, zero_smul]
      exact contDiff_const
    · refine ContDiff.const_smul _ ?_
      have ht' := clock_mem_window D G.level k t hτ hcc hcut
      have hwin := AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
      obtain ⟨_, _, hz3, _, _, hbox, _⟩ := hin.lift k hodd
      refine pulseMeanFluxEuler_contDiff _ _ _ n r _ _ _ _ _ t v s Mn.N depth hcc.ne'
        hin.stage.order (hrs r hr) hz3 ?_ ?_ ?_ ?_ ha ?_ ?_
      · exact fun hh' hH n' m α v u => (hbox hh' hH n' m α v u _ ht').1.mono hsX hsZ
      · intro k' j
        exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
          (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top)
      · intro k'
        exact (ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level) hodd _ k').of_le
          (by exact_mod_cast le_top)
      · intro hr0
        exact fiber_edge_boxSmooth G (hE ⟨r, hr, hr0⟩) k hodd _ _ t hcc.ne' hwin s
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
          (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top)
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
          (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top)
  · simp only [hodd, dite_false]
    exact contDiff_const

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
end
end
end

section
section
/-! Spatial regularity of the covariance-operator parts of the fluxes (the flux-regularity step, clauses 1 and 2).

* `covPolyP` of a `C^{n+2p}` field is `C^n`;
* `commFluxE` of a `C^{n+1}` field is `C^n` (the stream velocity is smooth);
* the temporal flux `menuTemporalFlux` and the mean flux `menuMeanFluxE ∘ P_p` are `C^{2p}`. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

open CovarianceTransport

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `P_p` of a `C^{n+2p}` field is `C^n`. -/
theorem covPolyP_contDiff (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p n : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ ((n + 2 * p : ℕ) : ℕ∞) f) : ContDiff ℝ (n : ℕ∞) (covPolyP Hc p f) := by
  have he : covPolyP Hc p f = fun x => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (covOperator Hc)^[l] f x := by
    funext x
    simp [covPolyP, Finset.sum_apply]
  rw [he]
  refine ContDiff.sum fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have := AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc l n f
    (hf.of_le (by exact_mod_cast (by omega : n + 2 * l ≤ n + 2 * p)))
  exact this.const_smul _

/-- `commFluxE` of a `C^{n+1}` field along a smooth velocity is `C^n`. -/
theorem commFluxE_contDiff (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) {g : Vec 2 → E}
    (hg : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) g) : ContDiff ℝ (n : ℕ∞) (commFluxE bv Hc g) := by
  have hjac : ∀ j k : Fin 2, ContDiff ℝ (n : ℕ∞) (fun x => jacMatrix bv x j k) := fun j k => by
    have := jacMatrix_entry_contDiff (s := n)
      (hbv.of_le (by exact_mod_cast le_top)) (g := fun y => y) contDiff_id j k
    exact this
  have hgrad : ∀ l : Fin 2, ContDiff ℝ (n : ℕ∞) (fun x => gradE g x l) := fun l =>
    (hg.fderiv_right (m := (n : ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply contDiff_const
  unfold commFluxE
  refine contDiff_pi.mpr fun j => ?_
  refine ContDiff.neg (ContDiff.sum fun l _ => ContDiff.smul ?_ (hgrad l))
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  exact ((((hjac j 0).mul contDiff_const).add ((hjac j 1).mul contDiff_const)).add
    ((contDiff_const.mul (hjac l 0)).add (contDiff_const.mul (hjac l 1))))

/-- The gradient of a `C^{n+1}` field is `C^n`. -/
theorem gradE_contDiff (n : ℕ) {g : Vec 2 → E} (hg : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) g)
    (l : Fin 2) : ContDiff ℝ (n : ℕ∞) (fun x => gradE g x l) :=
  (hg.fderiv_right (m := (n : ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-- The commutator part of the temporal flux is `C^{2p}` for a `C^{4p}` field. -/
theorem temporal_comm_contDiff (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 4 * p ≤ K) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) :
    ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fun x => ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
      ∑ a' ∈ Finset.range l, (covOperator Hc)^[a'] (commFluxE bv Hc
        ((covOperator Hc)^[l - 1 - a'] f)) x) := by
  refine ContDiff.sum fun l hl => ContDiff.const_smul _ (ContDiff.sum fun a' ha' => ?_)
  have hl' := Finset.mem_Icc.mp hl
  have ha'' := Finset.mem_range.mp ha'
  have h1 : ContDiff ℝ ((2 * p + 2 * a' + 1 : ℕ) : ℕ∞) ((covOperator Hc)^[l - 1 - a'] f) :=
    AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc (l - 1 - a')
      (2 * p + 2 * a' + 1) f (hf.of_le (by exact_mod_cast (by omega :
        2 * p + 2 * a' + 1 + 2 * (l - 1 - a') ≤ K)))
  have h2 := commFluxE_contDiff bv hbv Hc (2 * p + 2 * a') h1
  exact AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc a' (2 * p)
    _ h2

end Operators

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The floors of `SplitInput.range` give the orders needed at `s = 2p`. -/
theorem floors' (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) :
    2 * Mn.p + Dm ≤ Mn.sX ∧ 2 * Mn.p + Dm ≤ Mn.sZ := by
  obtain ⟨Dord, nMax, hMax, npad, _, _, _, _, _, h1, h2⟩ := hin.range
  have := le_max_right (Mn.N + Dord) (2 * Mn.p)
  omega

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **Clause 2: the mean flux of `P_p g` is `C^{2p}`.** -/
theorem menuMeanFluxE_contDiff (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT)
    (hE : (∃ r ∈ Finset.Icc 1 depth, r ≠ 0) → ActualFluxJointSmooth G) (K : ℕ)
    (hK : Mn.N + Dm + 4 * Mn.p ≤ K) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hg : ∀ v, ContDiff ℝ (K : ℕ∞) (fun x => g t x v)) (v : CompIn G.comps) :
    ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞) (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT
      (menuCovPRep Mn D G.level Mn.p g) t y v) := by
  obtain ⟨hX, hZ⟩ := floors' P Mn G G' depth CcT hin
  unfold menuMeanFluxE
  refine menuGluedMeanFlux_contDiff P Mn G G' depth CcT hin (2 * Mn.p) hX hZ _ _
    (fun r hr => (Finset.mem_Icc.mp hr).2) hE _ t ?_ v
  refine contDiff_pi.mpr fun w => ?_
  exact covPolyP_contDiff _ Mn.p _ ((hg w).of_le (by exact_mod_cast (by omega :
    2 * Mn.p + Dm + Mn.N + 2 * Mn.p ≤ K)))

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **Clause 1: the temporal flux is `C^{2p}`.** -/
theorem menuTemporalFlux_contDiff (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) (K : ℕ) (hK : Mn.N + Dm + 4 * Mn.p ≤ K)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hg : ∀ v, ContDiff ℝ (K : ℕ∞) (fun x => g t x v)) (v : CompIn G.comps) :
    ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞) (fun y => menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y) := by
  obtain ⟨hX, hZ⟩ := floors' P Mn G G' depth CcT hin
  have hord : 1 ≤ Dm := hin.stage.order
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff ℝ ((2 * Mn.p + Dm + Mn.N : ℕ) : ℕ∞) (menuCovPRep Mn D G.level Mn.p g t) := by
    refine contDiff_pi.mpr fun w => ?_
    exact covPolyP_contDiff _ Mn.p _ ((hg w).of_le (by exact_mod_cast (by omega :
      2 * Mn.p + Dm + Mn.N + 2 * Mn.p ≤ K)))
  have hga : ContDiff ℝ ((2 * Mn.p + 1 : ℕ) : ℕ∞) (fun y => menuCovPRep Mn D G.level Mn.p g t y v) :=
    covPolyP_contDiff _ Mn.p _ ((hg v).of_le (by exact_mod_cast (by omega :
      2 * Mn.p + 1 + 2 * Mn.p ≤ K)))
  unfold menuTemporalFlux menuDiagFluxPhys
  refine ContDiff.sub ?_ (ContDiff.sub ?_ ?_)
  · exact temporal_comm_contDiff _ hbv _ Mn.p K (by omega) (hg v)
  · exact menuGluedMeanFlux_contDiff P Mn G G' depth CcT hin (2 * Mn.p) hX hZ {0}
      (Finset.Icc 2 (Mn.N + 1)) (fun r hr => by simp at hr; omega)
      (fun ⟨r, hr, hr0⟩ => absurd (Finset.mem_singleton.mp hr) hr0)
      (menuCovPRep Mn D G.level Mn.p g) t ha v
  · refine contDiff_pi.mpr fun j => ContDiff.sum fun l _ => ContDiff.smul contDiff_const ?_
    exact gradE_contDiff (2 * Mn.p) hga l

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
end
end

section
/-! Self-contained tools of the Hilbert flux from arrays: `rootPathMap` of an appended map,
continuity from functionals, the source-flux coefficient as a good field, and the lifted edges
as good fields. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLTools

/-- A map into a finite-dimensional space is continuous when all its functionals are. -/
theorem hl_continuous_of_functionals {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : X → E}
    (h : ∀ ℓ : E →L[ℝ] ℝ, Continuous fun x => ℓ (f x)) : Continuous f := by
  let b := Module.finBasis ℝ E
  have : f = fun x => b.equivFunL.symm (fun i => (b.coord i).toContinuousLinearMap (f x)) := by
    funext x
    simp only [LinearMap.coe_toContinuousLinearMap']
    rw [show (fun i => b.coord i (f x)) = b.equivFun (f x) from rfl]
    simp
  rw [this]
  exact b.equivFunL.symm.continuous.comp (continuous_pi fun i => h _)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLTools
end
end

section
/-! Sources of the identities of the extended successor with another word: the source with
the word replaced, its validity, and the admissible words after appending a letter; the flux of
an identity of the extended successor does not depend on the word of its source (the lift
coefficients are unique on the windows where they are used, `liftAgreeOn_of_window`), so a copy has
the same coefficients in every word; the window data of the lift operators. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The same source with another word. -/
def reindexWithWord {G : GenStage D hr Dm b j₀} (w : List WordLetter) : SuccSource G → SuccSource G
  | .copyDir _ v u γ => .copyDir w v u γ
  | .copyQuad _ h π => .copyQuad w h π
  | .letterDiag _ u => .letterDiag w u
  | .letterMean _ n h π => .letterMean w n h π
  | .letterCov _ n h a a' π => .letterCov w n h a a' π

variable {G : GenStage D hr Dm b j₀}

theorem reindexWithWord_word (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).word = w := by cases s <;> rfl

theorem reindexWithWord_letter (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).letter? = s.letter? := by cases s <;> rfl

theorem reindexWithWord_oldSrc (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).oldSrc = s.oldSrc := by cases s <;> rfl

theorem reindexWithWord_oldTgt (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).oldTgt = s.oldTgt := by cases s <;> rfl

theorem reindexWithWord_prov (m : ℕ) (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).prov m = s.prov m := by cases s <;> rfl

theorem reindexWithWord_maps (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).maps = s.maps := by cases s <;> rfl

theorem reindexWithWord_lam (m : ℕ) (η : ℝ) (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).lam m η = s.lam m η := by cases s <;> rfl

theorem reindexWithWord_isDiag (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).IsDiag ↔ s.IsDiag := by cases s <;> simp [reindexWithWord, SuccSource.IsDiag]

theorem reindex_newWord_eq (s : SuccSource G) : s.newWord = s.word ++ s.letter?.toList := by
  unfold SuccSource.newWord
  cases h : s.letter? <;> simp

theorem reindexWithWord_newWord (w : List WordLetter) (s : SuccSource G) :
    (reindexWithWord w s).newWord = w ++ s.letter?.toList := by
  rw [reindex_newWord_eq, reindexWithWord_word, reindexWithWord_letter]

theorem reindexWithWord_valid {A : Finset WordLetter} {J : ℕ} {s : SuccSource G}
    (hs : s.Valid A J) {w : List WordLetter} (hw : w ∈ insert [] (wordsUpTo A (J + 1)))
    (hl : s.letter?.isSome → w.length ≤ J) : (reindexWithWord w s).Valid A J := by
  obtain ⟨-, h2, h3⟩ := hs
  cases s with
  | copyDir t v u γ => exact ⟨hw, fun l hl' => by simp [reindexWithWord, SuccSource.letter?] at hl', h3⟩
  | copyQuad t h π => exact ⟨hw, fun l hl' => by simp [reindexWithWord, SuccSource.letter?] at hl', h3⟩
  | letterDiag t u =>
    exact ⟨hw, fun l hl' => ⟨hl (by simp [SuccSource.letter?]),
      (h2 l hl').2⟩, h3⟩
  | letterMean t n h π =>
    exact ⟨hw, fun l hl' => ⟨hl (by simp [SuccSource.letter?]), (h2 l hl').2⟩, h3⟩
  | letterCov t n h a a' π =>
    exact ⟨hw, fun l hl' => ⟨hl (by simp [SuccSource.letter?]), (h2 l hl').2⟩, h3⟩

/-- Appending a letter of the alphabet to an admissible word of length at most `J`. -/
theorem reindex_word_snoc_mem {A : Finset WordLetter} {J : ℕ} {t : List WordLetter}
    (ht : t ∈ insert [] (wordsUpTo A (J + 1))) (hlen : t.length ≤ J) {l : WordLetter}
    (hl : l ∈ A) : t ++ [l] ∈ wordsUpTo A (J + 1) := by
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc]
  rcases Finset.mem_insert.1 ht with rfl | ht
  · refine ⟨1, ⟨le_rfl, by omega⟩, ?_⟩
    simp only [wordsOfLength, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
    exact ⟨(l, []), ⟨hl, rfl⟩, rfl⟩
  · simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc] at ht
    obtain ⟨k, hk, htk⟩ := ht
    have hk' : t.length = k := Providers.CascadeInvariants.length_of_mem_wordsOfLength htk
    refine ⟨k + 1, ⟨by omega, by omega⟩, ?_⟩
    simp only [wordsOfLength, Finset.mem_image, Finset.mem_product]
    exact ⟨(l, t), ⟨hl, htk⟩, rfl⟩

theorem reindexWithWord_self (s : SuccSource G) : reindexWithWord s.word s = s := by
  cases s <;> rfl

open AVRegularity.Uniqueness in
open scoped Classical in
/-- The coefficients of the finer output at the label `0` do not depend on the word of the source
(the lift coefficients are unique on the windows where they are used). -/
theorem reindex_fluxCoeff_withWord (Mn : SuccMenu) (hcs : 0 ≤ D.cellScaleSq G.level)
    (hτ : 0 < ocTau D.α D.q D.Λ G.level) (hW : Uniqueness.SuccWindowData D b j₀ Mn G)
    (hΩ : ∀ k A, IsAdmissibleChain D b j₀ G.level k A →
      IsOpen (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) ∧
        (0 : Vec 2) ∈ ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))
    (hΦ : ∀ (A : RealChain) (t : ℝ), ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : ∀ s : SuccSource G, s.IsLiftFamily Mn (Cc s)) (s : SuccSource G) (w : List WordLetter)
    (ρ s₀ : ℝ) (k : ℤ) (t : ℝ) (A : RealChain)
    (hk : ocCutoff D.α D.q D.Λ G.level k t ≠ 0) (d' : ℕ) (I' : DerivativeWord2 (d' - 1)) :
    fluxCoeff ((reindexWithWord w s).fluxOp ρ s₀ (Cc (reindexWithWord w s)) k t A) d' I' 0 =
      fluxCoeff (s.fluxOp ρ s₀ (Cc s) k t A) d' I' 0 := by
  have hsupp := cutoff_support D.α D.q D.Λ G.level k t hτ hk
  have hwin : ((D.cellScaleSq G.level)⁻¹ * t) ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    rcases hcs.eq_or_lt with hc0 | hcpos
    · rw [← hc0]
      simp
    · constructor
      · unfold OCData.slotStart
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hsupp.1 (inv_nonneg.mpr hcpos.le)
      · rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hsupp.2 (inv_nonneg.mpr hcpos.le)
  cases s with
  | copyDir t' v u γ => rfl
  | letterDiag t' u => rfl
  | copyQuad t' h π =>
    exact fluxOp_fluxCoeff_congr ρ s₀ (SuccSource.copyQuad t' h π) (Cc (reindexWithWord w (SuccSource.copyQuad t' h π))) (Cc (SuccSource.copyQuad t' h π)) k t A (fun hA => hΩ k A hA.1) (hΦ A t)
      (fun hA => liftAgreeOn_of_window Mn hcs hτ hW (SuccSource.copyQuad t' h π) (Cc (reindexWithWord w (SuccSource.copyQuad t' h π))) (Cc (SuccSource.copyQuad t' h π)) (hLF (reindexWithWord w (SuccSource.copyQuad t' h π))) (hLF (SuccSource.copyQuad t' h π)) k A hA (hΩ k A hA.1).1 _ hwin) d' I'
  | letterMean t' n h π =>
    exact fluxOp_fluxCoeff_congr ρ s₀ (SuccSource.letterMean t' n h π) (Cc (reindexWithWord w (SuccSource.letterMean t' n h π))) (Cc (SuccSource.letterMean t' n h π)) k t A (fun hA => hΩ k A hA.1) (hΦ A t)
      (fun hA => liftAgreeOn_of_window Mn hcs hτ hW (SuccSource.letterMean t' n h π) (Cc (reindexWithWord w (SuccSource.letterMean t' n h π))) (Cc (SuccSource.letterMean t' n h π)) (hLF (reindexWithWord w (SuccSource.letterMean t' n h π))) (hLF (SuccSource.letterMean t' n h π)) k A hA (hΩ k A hA.1).1 _ hwin) d' I'
  | letterCov t' n h a a' π =>
    exact fluxOp_fluxCoeff_congr ρ s₀ (SuccSource.letterCov t' n h a a' π) (Cc (reindexWithWord w (SuccSource.letterCov t' n h a a' π))) (Cc (SuccSource.letterCov t' n h a a' π)) k t A (fun hA => hΩ k A hA.1) (hΦ A t)
      (fun hA => liftAgreeOn_of_window Mn hcs hτ hW (SuccSource.letterCov t' n h a a' π) (Cc (reindexWithWord w (SuccSource.letterCov t' n h a a' π))) (Cc (SuccSource.letterCov t' n h a a' π)) (hLF (reindexWithWord w (SuccSource.letterCov t' n h a a' π))) (hLF (SuccSource.letterCov t' n h a a' π)) k A hA (hΩ k A hA.1).1 _ hwin) d' I'

open scoped Classical in
/-- **The flux of an identity does not depend on the word of its source**: two identities of the
extended successor whose sources differ only in the word have the same flux fields. -/
theorem reindex_flux_withWord (P : ProvParams) (Mn : SuccMenu) {G' : GenStage D hr Dm b j₀}
    (hcs : 0 ≤ D.cellScaleSq G.level) (hτ : 0 < ocTau D.α D.q D.Λ G.level)
    (hW : Uniqueness.SuccWindowData D b j₀ Mn G)
    (hΩ : ∀ k A, IsAdmissibleChain D b j₀ G.level k A →
      IsOpen (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) ∧
        (0 : Vec 2) ∈ ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))
    (hΦ : ∀ (A : RealChain) (t : ℝ), ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0)
    (W : SplitWitness P Mn G G') (v' u' v'' u'' : CompIn G'.comps) (γ : G'.fam.Γ v' u')
    (γ'' : G'.fam.Γ v'' u'') (w : List WordLetter)
    (hs : (W.e v' u' γ).1 = reindexWithWord w (W.e v'' u'' γ'').1) (p : OddSlot)
    (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) :
    G'.fam.flux p c v' u' γ d I t X z = G'.fam.flux p c v'' u'' γ'' d I t X z := by
  by_cases hd : 2 ≤ d
  swap
  · have h1 := G'.fam.flux_zero p c v' u' γ d I (fun h => hd h.1)
    have h2 := G'.fam.flux_zero p c v'' u'' γ'' d I (fun h => hd h.1)
    rw [h1, h2]
  obtain ⟨hp1, hmap1, hf1, hf1'⟩ := W.spec v' u' γ
  obtain ⟨hp2, hmap2, hf2, hf2'⟩ := W.spec v'' u'' γ''
  have hdg : (W.e v' u' γ).1.IsDiag ↔ (W.e v'' u'' γ'').1.IsDiag := by
    rw [hs, reindexWithWord_isDiag]
  by_cases hD : (W.e v'' u'' γ'').1.IsDiag
  · rw [hf1' (hdg.2 hD) p c d I t X z hd, hf2' hD p c d I t X z hd, hs, reindexWithWord_lam]
  · rw [hf1 (fun h => hD (hdg.1 h)) p c d I t X z hd, hf2 hD p c d I t X z hd, hs,
      reindexWithWord_lam, reindexWithWord_prov]
    by_cases hadm : IsAdmissibleChain D b j₀ G'.level p.1
        (c.1.recenter D (D.eps (G'.level - 1) • X))
    · simp only [hadm, ↓reduceIte]
      refine Uniqueness.transferAt_congr_coeff D G.level p _ _ _ _ t _ z d I (fun k hk A d' I' => ?_)
      exact reindex_fluxCoeff_withWord Mn hcs hτ hW hΩ hΦ W.Cc W.lifts _ w _ _ k t A hk d' I'
    · simp only [hadm, ↓reduceIte]

section Window

open AVRegularity.Providers AVRegularity.Providers.SuccWindow

/-- The sum of the absolute entries of a `2 × 2` matrix bounds each entry. -/
theorem reindex_entry_le_sum (F : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |F i j| ≤ |F 0 0| + |F 0 1| + |F 1 0| + |F 1 1| := by
  have h00 := abs_nonneg (F 0 0)
  have h01 := abs_nonneg (F 0 1)
  have h10 := abs_nonneg (F 1 0)
  have h11 := abs_nonneg (F 1 1)
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- A continuous matrix family has bounded entries on a compact interval. -/
theorem reindex_exists_entry_bound {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F)
    (a b : ℝ) : ∃ M : ℝ, ∀ t ∈ Set.Icc a b, ∀ i j, |F t i j| ≤ M := by
  have hc : Continuous (fun t => |F t 0 0| + |F t 0 1| + |F t 1 0| + |F t 1 1|) := by
    have he : ∀ i j : Fin 2, Continuous (fun t => F t i j) := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hF)
    fun_prop
  obtain ⟨M, -, hM⟩ := exists_bound_Icc hc a b
  refine ⟨M, fun t ht i j => (reindex_entry_le_sum (F t) i j).trans ?_⟩
  have := hM t ht
  rwa [abs_of_nonneg (by positivity)] at this

/-- **Window data of the lift operators of a stage**, without the positivity of the diffusivity
chain beyond the terminal level (the argument of `Providers.succ_window_data` does not use it). -/
theorem reindex_succ_window_data {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hζ : IsFastProfile D.ζ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) :
    AVRegularity.SuccWindowData D b j₀ Mn G := by
  intro h π k A hA X
  set ch := A.recenter D ((Mn.lenFactor * liftLength D G.level) • X) with hch
  set g := ch.geom D with hg
  have hC : ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r) :=
    geomC1_geom D hζ ch
  have hinv : AVRegularity.ChainGeometry.InvLaw g :=
    AVRegularity.ChainGeometry.invLaw_geomAux D _ _ _ (AVRegularity.ChainGeometry.invLaw_base D _ _ _)
  set c := D.cellScaleSq G.level with hc
  let F : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => ch.famJac D (c * t)
  have hFc : Continuous F :=
    (jac_continuous (f := fun u y => g.1 u y g.2.2) (hC g.2.2) g.2.1).comp
      (continuous_const.mul continuous_id)
  have hFdet : ∀ t, IsUnit (F t).det := fun t => jac_isUnit_det hinv hC (c * t) g.2.2 g.2.1
  have hAc : Continuous (fun t => (F t)⁻¹) := continuous_inv_of_det hFc hFdet
  set a₀ := D.slotStart G.level k / c
  set b₀ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / c
  obtain ⟨M, hM⟩ := reindex_exists_entry_bound hFc a₀ b₀
  obtain ⟨N, hN⟩ := reindex_exists_entry_bound hAc a₀ b₀
  obtain ⟨Mv, hMv⟩ := ocPulseCellDrift_bound (α := D.α) (q := D.q) (Λ := D.Λ) hζ G.level
    (D.kap G.level) hA.2
  refine ⟨(4 * M ^ 2 + 1)⁻¹, 2 * N ^ 2, Mv, by positivity, fun t ht ξ => ?_,
    fun t ht i j => ?_, fun t _ z j => hMv t z j⟩
  · exact metric_elliptic (Matrix.nonsing_inv_mul _ (hFdet t)) (hM t ht) ξ
  · exact metric_entry_le (hN t ht) i j

end Window

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The regularity of the covariance fluxes, the flux-regularity step of the flux cancellation split.

`covarianceFluxRegularity` proves `CovarianceFluxRegularityStatement` (clauses 1 and 2 from
`menuTemporalFlux_contDiff` and `menuMeanFluxE_contDiff`, clauses 3 and 5 from
`menuCovFlux_split_of_contDiff`) from the field `edge` of `SplitInput`: the joint smoothness of the
flux coefficients of `G` (`ActualFluxJointSmooth G`), used only for the grades `r ≥ 1` of
`𝐄^flux`. That fact follows (`actualFluxJointSmooth`) from slotwise transversality of `G` and the
reserve bounds `0 ≤ compReserve k v ≤ 2` for the context certificate `k`. The temporal flux
(clause 1) does not need it. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The joint smoothness of the flux coefficients of the actual contexts of `G`. -/
theorem actualFluxJointSmooth (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) :
    ActualFluxJointSmooth G := by
  obtain ⟨k, hG, hpar, hres⟩ := hin.edge
  have hi : 1 ≤ G.level := by have := hin.stage.level; omega
  have hε : 0 < D.eps (G.level - 1) := by
    unfold OCData.eps
    exact Construction.Stream.ocEpsilon_pos hin.stage.base
  intro p v u γ d I t ht n
  exact AVRegularity.Construction.Preservation.FullLift.native_actual_flux_joint_contDiff hG hpar
    hin.stage.natural hi (by have := hin.stage.level; omega) hin.stage.bandwidth hε p v u γ d I
    (hres v).1 (hres v).2 n t ht

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

open CovarianceTransport CovFluxReg

/-- **The flux-regularity step (regularity of the covariance flux)**. -/
theorem covarianceFluxRegularity : CovarianceFluxRegularityStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P seedK freshK φ₀ Mn G G' depth CcT hin K hK ta tb g hg v t ht
  have hg' : ∀ w, ContDiff ℝ (K : ℕ∞) (fun x => g t x w) := fun w => by
    have := (hg w t ht).1
    exact_mod_cast this
  have hT := menuTemporalFlux_contDiff P Mn G G' depth CcT hin K hK g t hg' v
  have hM := menuMeanFluxE_contDiff P Mn G G' depth CcT hin
    (fun _ => actualFluxJointSmooth P Mn G G' depth CcT hin)
    K hK g t hg' v
  have hT' : ContDiff ℝ (2 * Mn.p : ℕ) (fun y => menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y) := by
    exact_mod_cast hT
  have hM' : ContDiff ℝ (2 * Mn.p : ℕ) (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT
      (menuCovPRep Mn D G.level Mn.p g) t y v) := by
    exact_mod_cast hM
  exact ⟨hT', hM', menuCovFlux_split_of_contDiff Mn G G.level Mn.N Mn.p depth CcT g v t hT' hM'⟩

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step (jet locality of `Q_p 𝐄^flux P_p`): the steps**.

`CovMeanJetStatement` is reduced to three statements:

* `CovPolyPJetStatement` (inner, `P_p`): `𝖯_p` is a differential operator of order `≤ 2p` with
  constant coefficients, so two `C^{s+2p}` functions with the same jets of the orders `≤ s + 2p` at
  `x` give `C^s` functions with the same jets of the orders `≤ s` at `x`;
* `CovPolyQJetStatement` (outer, `Q_p`): two `C^{2p}` functions with the same jets of the orders
  `≤ 2p` at `x` have the same `𝖰_p` at `x`;
* `MenuMeanFluxJetStatement` (the traversal of `liftFluxX`): for coarse fields `a₁, a₂` of class
  `C^s`, `s ≥ N + Dm + 2p`, at the time `t`, with the same jets of the orders `≤ s` at `x`, the
  fluxes `y ↦ 𝐄^flux a_i (t, y)` have the same jets of the orders `≤ 2p` at `x` (their `C^{2p}`
  regularity is the `menuMeanFluxE_contDiff`).

If `a₂ = 0` and `a₁` is flat of order `s` at `x`, the flux is flat of order `2p`; for `p = 0`
one has `s ≥ N + Dm - 1` and `𝖯_0 = 𝖰_0 = id`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- The functions `f, g` have the same ordered derivatives of the orders `≤ s` at `x`. -/
def SameJetAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℕ) (x : Vec 2)
    (f g : Vec 2 → E) : Prop :=
  ∀ (r : ℕ) (I : DerivativeWord2 r), r ≤ s → orderedDerivative I f x = orderedDerivative I g x

/-- **Inner step (`P_p`).** -/
def CovPolyPJetStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p s : ℕ)
    (x : Vec 2) (f g : Vec 2 → E), ContDiff ℝ (↑(s + 2 * p) : ℕ∞) f →
    ContDiff ℝ (↑(s + 2 * p) : ℕ∞) g → SameJetAt (s + 2 * p) x f g →
    ContDiff ℝ (↑s : ℕ∞) (covPolyP Hc p f) ∧ ContDiff ℝ (↑s : ℕ∞) (covPolyP Hc p g) ∧
      SameJetAt s x (covPolyP Hc p f) (covPolyP Hc p g)

/-- **Outer step (`Q_p`).** -/
def CovPolyQJetStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (x : Vec 2) (f g : Vec 2 → E), ContDiff ℝ (↑(2 * p) : ℕ∞) f → ContDiff ℝ (↑(2 * p) : ℕ∞) g →
    SameJetAt (2 * p) x f g → covPolyQ Hc p f x = covPolyQ Hc p g x

/-- **The traversal of `liftFluxX`.** -/
def MenuMeanFluxJetStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (s : ℕ), Mn.N + Dm + 2 * Mn.p ≤ s →
    ∀ (t : ℝ) (x : Vec 2) (a₁ a₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (↑s : ℕ∞) (fun y => a₁ t y v)) →
      (∀ v, ContDiff ℝ (↑s : ℕ∞) (fun y => a₂ t y v)) →
      (∀ v, SameJetAt s x (fun y => a₁ t y v) (fun y => a₂ t y v)) →
      ∀ v : CompIn G.comps,
        SameJetAt (2 * Mn.p) x (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT a₁ t y v)
          (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT a₂ t y v)

/-- `CovMeanJetStatement` from its three steps. -/
theorem covMeanJet_of_steps (hP : CovPolyPJetStatement) (hQ : CovPolyQJetStatement)
    (hM : MenuMeanFluxJetStatement) : CovMeanJetStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin K hK t x g₁ g₂ h₁ h₂ hj v
  have hKe : K = (K - 2 * Mn.p) + 2 * Mn.p := by omega
  have hP' : ∀ w, ContDiff ℝ (↑(K - 2 * Mn.p) : ℕ∞)
        (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (fun y => g₁ t y w)) ∧
      ContDiff ℝ (↑(K - 2 * Mn.p) : ℕ∞)
        (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (fun y => g₂ t y w)) ∧
      SameJetAt (K - 2 * Mn.p) x
        (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (fun y => g₁ t y w))
        (covPolyP (menuCovPrimitive D Mn G.level t) Mn.p (fun y => g₂ t y w)) := by
    intro w
    have := @hP (hr w.1.root) _ _ (menuCovPrimitive D Mn G.level t) Mn.p (K - 2 * Mn.p) x
      (fun y => g₁ t y w) (fun y => g₂ t y w)
    rw [← hKe] at this
    exact this (h₁ w) (h₂ w) (fun r I hr' => hj w r I hr')
  have hM3 := hM P Mn G G' depth CcT hin (K - 2 * Mn.p) (by omega) t x
    (menuCovPRep Mn D G.level Mn.p g₁) (menuCovPRep Mn D G.level Mn.p g₂)
    (fun w => (hP' w).1) (fun w => (hP' w).2.1) (fun w => (hP' w).2.2) v
  have hE : (∃ r ∈ Finset.Icc 1 depth, r ≠ 0) → CovFluxReg.ActualFluxJointSmooth G := fun _ =>
    CovFluxReg.actualFluxJointSmooth P Mn G G' depth CcT hin
  have hM1 : ContDiff ℝ (↑(2 * Mn.p) : ℕ∞) (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT
      (menuCovPRep Mn D G.level Mn.p g₁) t y v) := by
    exact_mod_cast CovFluxReg.menuMeanFluxE_contDiff P Mn G G' depth CcT hin hE K hK g₁ t h₁ v
  have hM2 : ContDiff ℝ (↑(2 * Mn.p) : ℕ∞) (fun y => menuMeanFluxE Mn G G.level Mn.N depth CcT
      (menuCovPRep Mn D G.level Mn.p g₂) t y v) := by
    exact_mod_cast CovFluxReg.menuMeanFluxE_contDiff P Mn G G' depth CcT hin hE K hK g₂ t h₂ v
  exact congrArg toFluxL (hQ _ Mn.p x _ _ hM1 hM2 hM3)
end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
