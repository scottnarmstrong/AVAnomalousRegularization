-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.Mean.Transfer
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

/-! Bookkeeping for the native weak mean sum. The construction starts from the
single scalar root, and every weak extension retains that root. Its actual edge
maps and hence its ordered path maps are scalar identities. The source registry
is the already proved equivalence of the passage witness. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Residual.Presentation

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Every component in the downward weak construction has the original scalar root. -/
theorem Case.componentRoot (x : Case plan R) (j : ℕ) (hj : x.c.M ≤ j)
    (hjt : j ≤ x.c.M + A.Jw) (v : CompIn (x.c.stage j).comps) : v.1.root = 0 := by
  classical
  have hroot : ∀ k, k ≤ A.Jw → ∀ u ∈ (x.c.stage (x.c.M + A.Jw - k)).comps,
      u.root = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ u hu
      simp only [Nat.sub_zero] at hu
      rw [x.c.construction.2.1.2.1] at hu
      have he : u = ⟨0, []⟩ := Finset.mem_singleton.mp hu
      rw [he]
    | succ k ih =>
      intro hk u hu
      have hi : x.c.M < x.c.M + A.Jw - k := by omega
      have hit : x.c.M + A.Jw - k ≤ x.c.M + A.Jw := Nat.sub_le _ _
      have he : x.c.M + A.Jw - (k + 1) = x.c.M + A.Jw - k - 1 := by omega
      rw [he, cd_comps_eq x.c (x.c.M + A.Jw - k) hi hit] at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact ih (by omega) u hu
      · obtain ⟨⟨a, w⟩, haw, rfl⟩ := Finset.mem_image.mp hu
        rw [cd_succComp_root]
        exact ih (by omega) a (Finset.mem_product.mp haw).1
  have he : x.c.M + A.Jw - (x.c.M + A.Jw - j) = j := by omega
  have h := hroot (x.c.M + A.Jw - j) (by omega)
  rw [he] at h
  exact h v.1 v.2

/-- The incoming weak edge maps are scalar identities, including the empty root graph. -/
theorem Case.incomingEdgeMap (x : Case plan R) (v u : CompIn (x.c.stage x.i).comps)
    (γ : (x.c.stage x.i).fam.Γ v u) :
    ((x.c.stage x.i).fam.identity v u γ).map = ContinuousLinearMap.id ℝ ℝ := by
  classical
  by_cases heq : x.i = x.c.M + A.Jw
  · have he : IsEmpty ((x.c.stage x.i).fam.Γ v u) := by
      have hh := x.c.construction.2.1.2.2.1
      rw [← heq] at hh
      exact hh v u
    exact he.false γ |>.elim
  · have hi : x.c.M < x.i + 1 := by have := x.lower; omega
    have hit : x.i + 1 ≤ x.c.M + A.Jw := by have := x.upper; omega
    have he : x.i + 1 - 1 = x.i := by omega
    have hm := cd_edge_map x.c (x.i + 1) hi hit
    rw [he] at hm
    rw [hm v u γ, cd_rootPathMap_nil, x.componentRoot x.i x.lower.le x.upper u,
      x.componentRoot x.i x.lower.le x.upper v, ite_eq_left rfl]

private theorem weakMean_rootPathMap_replicate (n : ℕ) :
    rootPathMap ScalarH 0 (List.replicate n ⟨0, 0, ContinuousLinearMap.id ℝ ℝ⟩) 0 =
      ContinuousLinearMap.id ℝ ℝ := by
  induction n with
  | zero => simp only [List.replicate_zero, rootPathMap, dite_true]
  | succ n ih =>
    simp only [List.replicate_succ, rootPathMap, dite_true, ih,
      ContinuousLinearMap.id_comp]

/-- Each native weak path has the identity scalar map. -/
theorem Case.pathMap (x : Case plan R) {g : ℕ}
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g) :
    rootPathMap ScalarH π.src.root π.mapList π.tgt.root = ContinuousLinearMap.id ℝ ℝ := by
  classical
  have hstep : ∀ j : Fin g,
      (⟨(π.step j).2.1.1.root, (π.step j).1.1.root,
        ((weakWindowStage x.c x.i x.lower x.upper).fam.identity _ _ (π.step j).2.2).map⟩ :
          Σ (a b : ℕ), ScalarH a →L[ℝ] ScalarH b) =
      ⟨0, 0, ContinuousLinearMap.id ℝ ℝ⟩ := by
    intro j
    have hs := x.componentRoot x.i x.lower.le x.upper (π.step j).2.1
    have ht := x.componentRoot x.i x.lower.le x.upper (π.step j).1
    have hm : ((weakWindowStage x.c x.i x.lower x.upper).fam.identity _ _
        (π.step j).2.2).map = ContinuousLinearMap.id ℝ ℝ :=
      x.incomingEdgeMap (π.step j).1 (π.step j).2.1 (π.step j).2.2
    rw [hm, hs, ht]
  have hlist : π.mapList = List.replicate g ⟨0, 0, ContinuousLinearMap.id ℝ ℝ⟩ := by
    unfold StagePath.mapList
    simp_rw [hstep]
    exact List.ofFn_const g _
  have hsrc : π.src.root = 0 := by
    unfold StagePath.src
    split_ifs with hg
    · exact x.componentRoot x.i x.lower.le x.upper (π.step ⟨0, hg⟩).2.1
    · rfl
  have htgt : π.tgt.root = 0 := by
    unfold StagePath.tgt
    split_ifs with hg
    · exact x.componentRoot x.i x.lower.le x.upper (π.step ⟨g - 1, by omega⟩).1
    · rfl
  rw [hlist, hsrc, htgt]
  exact weakMean_rootPathMap_replicate g

/-- Every degree/word selection of a path source gives its original native sequence. -/
theorem Case.selectedPathSequence (x : Case plan R) {g : ℕ}
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (w : List WordLetter) (n : ℕ) :
    IsLiftSequence (x.pathData π k hk (x.native k hk hj)) R.sX R.sZ
      (x.left k) (x.right k) A.Nw g (x.pathCoefficients π k hk (x.native k hk hj) w n) := by
  have hl := x.pathSequenceOn π k hk (x.native k hk hj) w n
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  rw [heps] at hl
  have hΩ : ladderOmega x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (x.native k hk hj).1 x.length = Set.univ := x.nativeLadder_univ k hk hj
  rw [hΩ] at hl
  have h := liftSequence_of_on_univ _ _ _ _ _ _ _ _ hl
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  simpa only [Case.left, Case.right, weakSlotLeft, weakSlotRight, hlevel] using h

/-- Selecting a different source degree or word does not change its native path mean. -/
theorem Case.pathMeanChoice (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (w : List WordLetter) (n₀ n : ℕ) (t : ℝ)
    (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈ Icc (x.left k) (x.right k)) :
    pathMeanFlux x.c.D (x.c.stage x.i).level x.length
      (x.pathData π k hk (x.native k hk hj))
      (x.pathCoefficients π k hk (x.native k hk hj) w n₀) n t =
    pathMeanFlux x.c.D (x.c.stage x.i).level x.length
      (x.pathData π k hk (x.native k hk hj))
      (x.pathCoefficients π k hk (x.native k hk hj)) n t := by
  let Q := x.pathData π k hk (x.native k hk hj)
  have H := x.pathSetting hcommon k hk hj hX hZ
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  have hW : ∀ X, ∃ lo hi Mv : ℝ, Uniqueness.WindowData
      (fun t => Matrix.of (Q.G t X)) Q.v (x.left k) (x.right k) lo hi Mv :=
    by
      intro X
      simpa only [Q, Case.pathData, heps, Case.native, familyLiftData] using H.windowData X
  have he := Uniqueness.lift_sequence_unique_window Q (x.left k) (x.right k)
    H.window hW R.sX R.sZ A.Nw g _ _ (x.selectedPathSequence π k hk hj w n₀)
      (x.selectedPathSequence π k hk hj [] 2)
  refine Uniqueness.pathMeanFlux_congr x.c.D (x.c.stage x.i).level x.length Q _ _ n t ?_
  intro hh hhh n' m α
  funext X z v u
  exact he hh hhh n' m α _ ht X z v u

/-- An incoming component, retained without a word in the output stage. -/
def Case.retained (x : Case plan R) (v : CompIn (x.c.stage x.i).comps) :
    CompIn (x.c.stage (x.i - 1)).comps :=
  ⟨v.1, by rw [cd_comps_eq x.c x.i x.lower x.upper]; exact Finset.mem_union_left _ v.2⟩

/-- The finite degrees and paths of one inherited grade between retained components. -/
abbrev Case.inheritedIndex (x : Case plan R) (g : ℕ)
    (u v : CompIn (x.c.stage x.i).comps) :=
  Finset.Icc 2 (A.Nw + x.incomingOrder) ×
    {π : StagePath (x.c.stage x.i) g // π.src = u.1 ∧ π.tgt = v.1}

/-- The actual valid source corresponding to a degree and path at the empty word. -/
def Case.inheritedSource (x : Case plan R) {g : ℕ} (hg : 1 ≤ g)
    (u v : CompIn (x.c.stage x.i).comps) (a : x.inheritedIndex g u v) :
    {s : WeakSource (x.c.stage x.i) // s.Valid A.Nw A.Rw x.incomingOrder ∧
      s.srcComp (x.c.stage x.i).level = (x.retained u).1 ∧
      s.tgtComp (x.c.stage x.i).level = (x.retained v).1} :=
  ⟨.inherited [] g a.2.1 a.1.1,
    ⟨⟨Or.inl rfl, hg, (Finset.mem_Icc.mp a.1.2).1, (Finset.mem_Icc.mp a.1.2).2⟩,
      by simp only [WeakSource.srcComp, succComp, dite_true, a.2.2.1, Case.retained],
      by simp only [WeakSource.tgtComp, succComp, dite_true, a.2.2.2, Case.retained]⟩⟩

/-- The stored inherited edges of a fixed grade are exactly its paths and retained degrees. -/
def Case.inheritedRegistryEquiv (x : Case plan R) {g : ℕ} (hg : 1 ≤ g)
    (u v : CompIn (x.c.stage x.i).comps) :
    x.inheritedIndex g u v ≃
      {γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u) //
        cdIsGrade g (x.witness.e (x.retained v) (x.retained u) γ).1} := by
  classical
  let e := x.witness.e (x.retained v) (x.retained u)
  let f : x.inheritedIndex g u v →
      {γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u) //
        cdIsGrade g (e γ).1} := fun a =>
    ⟨e.symm (x.inheritedSource hg u v a), by rw [e.apply_symm_apply]; exact rfl⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have he := congrArg (fun γ => (e γ).1) (congrArg Subtype.val hab)
    change (e (e.symm (x.inheritedSource hg u v a))).1 =
      (e (e.symm (x.inheritedSource hg u v b))).1 at he
    rw [e.apply_symm_apply, e.apply_symm_apply] at he
    have hi : a.2.1 = b.2.1 ∧ a.1.1 = b.1.1 := by
      change WeakSource.inherited [] g a.2.1 a.1.1 = WeakSource.inherited [] g b.2.1 b.1.1 at he
      simpa using (WeakSource.inherited.inj he)
    exact Prod.ext (Subtype.ext hi.2) (Subtype.ext hi.1)
  · intro γ
    have hsrc := (e γ.1).2
    have hsrc' : (e γ.1).1.Valid A.Nw A.Rw x.incomingOrder ∧
        (e γ.1).1.srcComp (x.c.stage x.i).level = succComp x.i u.1 [] ∧
        (e γ.1).1.tgtComp (x.c.stage x.i).level = succComp x.i v.1 [] := by
      simpa only [succComp, dite_true, Case.retained] using hsrc
    obtain ⟨h, π, n, hs, hπs, hπt, _, hh, hn, hn'⟩ :=
      cd_inh_shape x.c x.i x.lower x.upper u v [] (e γ.1).1 hsrc'
    have heq : h = g := by
      have hgrade : cdIsGrade g (e γ.1).1 := γ.2
      rw [hs] at hgrade
      exact hgrade
    subst h
    let a : x.inheritedIndex g u v := ⟨⟨n, Finset.mem_Icc.mpr ⟨hn, hn'⟩⟩, ⟨π, hπs, hπt⟩⟩
    refine ⟨a, Subtype.ext ?_⟩
    apply e.injective
    change e (e.symm (x.inheritedSource hg u v a)) = e γ.1
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hs.symm

/-- The source of the registry bijection is its specified degree/path source. -/
theorem Case.inheritedRegistryEquiv_source (x : Case plan R) {g : ℕ} (hg : 1 ≤ g)
    (u v : CompIn (x.c.stage x.i).comps) (a : x.inheritedIndex g u v) :
    (x.witness.e (x.retained v) (x.retained u)
      ((x.inheritedRegistryEquiv hg u v) a).1).1 =
        WeakSource.inherited [] g a.2.1 a.1.1 := by
  change ((x.witness.e (x.retained v) (x.retained u))
    ((x.witness.e (x.retained v) (x.retained u)).symm (x.inheritedSource hg u v a))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

open scoped Classical in
/-- Finite reindexing of every inherited grade by its path and its retained degree. -/
theorem Case.inheritedRegistrySum (x : Case plan R) {g : ℕ} (hg : 1 ≤ g)
    (u v : CompIn (x.c.stage x.i).comps) {E : Type*} [AddCommMonoid E]
    (F : WeakSource (x.c.stage x.i) → E) :
    (∑ γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u),
      if cdIsGrade g (x.witness.e (x.retained v) (x.retained u) γ).1 then
        F (x.witness.e (x.retained v) (x.retained u) γ).1 else 0) =
      ∑ᶠ a : x.inheritedIndex g u v, F (.inherited [] g a.2.1 a.1.1) := by
  classical
  let : Fintype (x.inheritedIndex g u v) := Fintype.ofFinite _
  let e := x.witness.e (x.retained v) (x.retained u)
  let p := fun γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u) =>
    cdIsGrade g (e γ).1
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun γ => by simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]) (fun γ => F (e γ).1)]
  rw [← (x.inheritedRegistryEquiv hg u v).sum_comp (fun γ => F (e γ.1).1)]
  exact Finset.sum_congr rfl fun a _ => congrArg F (x.inheritedRegistryEquiv_source hg u v a)

/-- The outgoing weak edge maps also have the original scalar identity. -/
theorem Case.outgoingEdgeMap (x : Case plan R)
    (v u : CompIn (x.c.stage (x.i - 1)).comps)
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) :
    ((x.c.stage (x.i - 1)).fam.identity v u γ).map = ContinuousLinearMap.id ℝ ℝ := by
  rw [cd_edge_map x.c x.i x.lower x.upper v u γ, cd_rootPathMap_nil,
    x.componentRoot (x.i - 1) (by have := x.lower; omega)
      ((Nat.sub_le _ _).trans x.upper) u,
    x.componentRoot (x.i - 1) (by have := x.lower; omega)
      ((Nat.sub_le _ _).trans x.upper) v, ite_eq_left rfl]

/-- Reading an actual stored weak edge on a smooth scalar field gives its glued source. -/
theorem Case.edgePhysicalAction (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (v u : CompIn (x.c.stage (x.i - 1)).comps)
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) (t : ℝ) (Dc : ℕ)
    (hDc : (x.witness.e v u γ).1.degree ≤ Dc)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) (j : Fin 2) :
    (∑ d ∈ Finset.Icc 2 Dc, (x.c.stage (x.i - 1)).physCoeff v u γ d t y
      (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j) =
      (x.witness.e v u γ).1.lam (x.c.stage x.i).level A.η₀ * x.sourceEuler γ t f y j := by
  rw [x.edgePhysicalFlux hcommon hX hZ v u γ t Dc f hf y j, x.outgoingEdgeMap v u γ]
  change (x.witness.e v u γ).1.lam (x.c.stage x.i).level A.η₀ *
      (∑ d ∈ Finset.Icc 2 Dc, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (x.sourceEuler γ t) d I y j * orderedDerivative I f y) = _
  rw [← x.sourceEulerExpansion hcommon hX hZ γ t Dc hDc f hf y j]

/-- The glued finer flux operator indexed directly by a source. -/
abbrev Case.sourceEulerOf (x : Case plan R) (s : WeakSource (x.c.stage x.i)) (t : ℝ) :=
  gluedFluxOp x.c.D (x.c.stage x.i).level
    (fun k => s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
      (nativeChain (x.c.stage x.i).level k)) t

/-- Contracting the stored CE block is precisely the finite sum of its native path sources. -/
theorem Case.cePhysicalAction (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (hg : 1 ≤ g) (u v : CompIn (x.c.stage x.i).comps)
    (Dc : ℕ) (hDc : x.cap ≤ Dc) (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ d : Finset.Icc 2 Dc, cdCE x.c Dc x.i x.lower x.upper g v u d t y
      (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j) =
      ∑ᶠ a : x.inheritedIndex g u v,
        x.sourceEulerOf (.inherited [] g a.2.1 a.1.1) t f y j := by
  classical
  let e := x.witness.e (x.retained v) (x.retained u)
  let F := fun s : WeakSource (x.c.stage x.i) =>
    s.lam (x.c.stage x.i).level A.η₀ * x.sourceEulerOf s t f y j
  have hmem : v.1 ∈ (x.c.stage (x.i - 1)).comps ∧ u.1 ∈ (x.c.stage (x.i - 1)).comps :=
    ⟨(x.retained v).2, (x.retained u).2⟩
  have heq (d : Finset.Icc 2 Dc) :
      cdCE x.c Dc x.i x.lower x.upper g v u d t y
        (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j =
      ∑ γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u),
        if cdIsGrade g (e γ).1 then
          (x.c.stage (x.i - 1)).physCoeff (x.retained v) (x.retained u) γ d.1 t y
            (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j else 0 := by
    have hcoef : cdCE x.c Dc x.i x.lower x.upper g v u d t y =
        ∑ γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u),
          if cdIsGrade g (e γ).1 then
            (x.c.stage (x.i - 1)).physCoeff (x.retained v) (x.retained u) γ d.1 t y else 0 := by
      unfold cdCE
      rw [dite_eq_left hmem]
      change (∑ γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u),
        if cdIsGrade g (cdEdgeSource x.c x.i x.lower x.upper
          (x.retained v) (x.retained u) γ).1 then
          (x.c.stage (x.i - 1)).physCoeff (x.retained v) (x.retained u) γ d.1 t y else 0) = _
      rw [← x.witness_edge (x.retained v) (x.retained u)]
    rw [hcoef]
    simp only [_root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun γ _ => by split_ifs <;> rfl
  simp_rw [heq]
  rw [Finset.sum_comm]
  have hterm (γ : (x.c.stage (x.i - 1)).fam.Γ (x.retained v) (x.retained u)) :
      (∑ d : Finset.Icc 2 Dc, if cdIsGrade g (e γ).1 then
        (x.c.stage (x.i - 1)).physCoeff (x.retained v) (x.retained u) γ d.1 t y
          (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j else 0) =
        if cdIsGrade g (e γ).1 then F (e γ).1 else 0 := by
    by_cases hγ : cdIsGrade g (e γ).1
    · simp only [hγ, ite_true]
      rw [Finset.sum_coe_sort (Finset.Icc 2 Dc) (fun d : ℕ =>
        (x.c.stage (x.i - 1)).physCoeff (x.retained v) (x.retained u) γ d t y
          (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j)]
      exact x.edgePhysicalAction hcommon hX hZ (x.retained v) (x.retained u) γ t Dc
        ((x.validDegree (e γ).1 (e γ).2.1).2.trans hDc) f hf y j
    · simp only [hγ, ite_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun γ _ => hterm γ, x.inheritedRegistrySum hg u v F]
  exact finsum_congr fun a => by simp only [F, WeakSource.lam, one_mul]

/-- The normalized AD block contracts to the finite collection of scalar eddy sources. -/
theorem Case.adPhysicalAction (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (Dc : ℕ) (hDc : x.cap ≤ Dc) (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ d : Finset.Icc 2 Dc, cdAD x.c Dc x.i x.v₀ d t y
      (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j) =
      ∑ n ∈ Finset.Icc 2 (A.Nw + 1),
        x.sourceEulerOf (.eddy x.v₀ [] n) t f y j := by
  classical
  have hRw : 0 < A.Rw := x.response
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hmem (n : ℕ) (hn : n ∈ Finset.Icc 2 (A.Nw + 1)) :
      x.v₀.1 ∈ (x.c.stage (x.i - 1)).comps ∧
        succComp x.i x.v₀.1 [WordLetter.eddy n] ∈ (x.c.stage (x.i - 1)).comps := by
    refine ⟨(x.retained x.v₀).2, ?_⟩
    exact cd_succComp_mem x.c x.i x.lower x.upper x.v₀ [WordLetter.eddy n]
      (Or.inr (cd_append_mem A.Nw A.Rw [] n (Or.inl rfl) hRw
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2))
  unfold cdAD
  simp only [_root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hmn := hmem n hn
  simp only [dite_eq_left hmn]
  let v' : CompIn (x.c.stage (x.i - 1)).comps :=
    ⟨succComp x.i x.v₀.1 [WordLetter.eddy n], hmn.2⟩
  let u' : CompIn (x.c.stage (x.i - 1)).comps := ⟨x.v₀.1, hmn.1⟩
  obtain ⟨γ, hγ⟩ := cd_eddy_edge_exists x.c x.i x.lower x.upper v' u' x.v₀ [] n
    (Or.inl rfl) hRw (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    (by simp only [succComp, dite_true, u']) rfl
  have hsource : (x.witness.e v' u' γ).1 = .eddy x.v₀ [] n := by
    rw [x.witness_edge v' u']; exact hγ
  have hb := (cd_stage_inv x.c x.i x.lower x.upper).2
  have hword := Construction.Preservation.FullLift.parent_word_succComp
    (m := x.i) (by have := x.lower; omega) x.v₀.1 (hb _ x.v₀.2) [WordLetter.eddy n]
  have hroot := InitialValue.compParent_eq_self (m := x.i)
    (by have := x.lower; omega) (hb _ x.v₀.2)
  have hne : compWord x.i v'.1 ≠ compWord x.i u'.1 := by
    rw [show v'.1 = succComp x.i x.v₀.1 [WordLetter.eddy n] from rfl, hword.2,
      show u'.1 = x.v₀.1 from rfl, hroot.2]
    intro he
    have hl := congrArg List.length he
    norm_num at hl
  have hsum (d : Finset.Icc 2 Dc) :
      (∑ γ' : (x.c.stage (x.i - 1)).fam.Γ v' u',
        ((x.c.D.eps (x.i - 1) ^ A.η₀) •
          (x.c.stage (x.i - 1)).physCoeff v' u' γ' d.1 t y)
            (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j) =
      x.c.D.eps (x.i - 1) ^ A.η₀ *
        (x.c.stage (x.i - 1)).physCoeff v' u' γ d.1 t y
          (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j := by
    rw [cd_eddy_sum_all x.c x.i x.lower x.upper hne γ hγ]
    rfl
  simp only [_root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ d : Finset.Icc 2 Dc, ∑ γ' : (x.c.stage (x.i - 1)).fam.Γ v' u',
    ((x.c.D.eps (x.i - 1) ^ A.η₀) •
      (x.c.stage (x.i - 1)).physCoeff v' u' γ' d.1 t y)
        (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j) = _
  rw [Finset.sum_congr rfl fun d _ => hsum d, ← Finset.mul_sum]
  rw [Finset.sum_coe_sort (Finset.Icc 2 Dc) (fun d : ℕ =>
    (x.c.stage (x.i - 1)).physCoeff v' u' γ d t y
      (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j)]
  rw [x.edgePhysicalAction hcommon hX hZ v' u' γ t Dc
    ((x.validDegree _ (x.witness.e v' u' γ).2.1).2.trans hDc) f hf y j]
  change x.c.D.eps (x.i - 1) ^ A.η₀ *
    ((x.witness.e v' u' γ).1.lam (x.c.stage x.i).level A.η₀ *
      x.sourceEulerOf (x.witness.e v' u' γ).1 t f y j) = _
  rw [hsource, WeakSource.lam, hlevel, Real.rpow_neg (x.scales hcommon).2.le,
    ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (x.scales hcommon).2 A.η₀).ne', one_mul]

/-- Summing the inherited registry over input components is summing paths into the output. -/
theorem Case.inheritedComponentsSum (x : Case plan R) {g : ℕ} (hg : 1 ≤ g)
    (v : CompIn (x.c.stage x.i).comps) {E : Type*} [AddCommMonoid E]
    (F : StagePath (x.c.stage x.i) g → ℕ → E) :
    (∑ u : CompIn (x.c.stage x.i).comps,
      ∑ᶠ a : x.inheritedIndex g u v, F a.2.1 a.1.1) =
      ∑ n ∈ Finset.Icc 2 (A.Nw + x.incomingOrder),
        ∑ᶠ π : StagePath (x.c.stage x.i) g, if π.tgt = v.1 then F π n else 0 := by
  classical
  let : Fintype (StagePath (x.c.stage x.i) g) := Fintype.ofFinite _
  simp only [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_coe_sort (Finset.Icc 2 (A.Nw + x.incomingOrder))
    (fun n : ℕ => ∑ u : CompIn (x.c.stage x.i).comps,
      ∑ π : {π : StagePath (x.c.stage x.i) g // π.src = u.1 ∧ π.tgt = v.1}, F π.1 n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hterm (u : CompIn (x.c.stage x.i).comps) :
      (∑ π : {π : StagePath (x.c.stage x.i) g // π.src = u.1 ∧ π.tgt = v.1}, F π.1 n) =
        ∑ π : StagePath (x.c.stage x.i) g,
          if π.src = u.1 ∧ π.tgt = v.1 then F π n else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun π : StagePath (x.c.stage x.i) g =>
      π.src = u.1 ∧ π.tgt = v.1)
      (Finset.univ.filter (fun π => π.src = u.1 ∧ π.tgt = v.1))
      (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun π => F π n)).symm
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  let u₀ : CompIn (x.c.stage x.i).comps := ⟨π.src, (cd_stagePath_mem x.c x.i π hg).1⟩
  rw [Finset.sum_eq_single u₀]
  · simp only [u₀, eq_self, true_and]
  · intro u _ hne
    have hsrc : π.src ≠ u.1 := fun he => hne (Subtype.ext he.symm)
    simp only [hsrc, false_and, ite_false]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- A native observed weight is the construction's cutoff. -/
theorem Case.pulseWeight (x : Case plan R) (k : ℤ) (hk : Odd k) (t : ℝ) :
    x.weight k t = ocCutoff x.c.D.α x.c.D.q x.c.D.Λ x.i k t := by
  change (x.c.stage x.i).fam.weight (oddSlotOf k) t = _
  rw [oddSlotOf_of_odd hk, x.natural.2.1, (cd_stage_inv x.c x.i x.lower x.upper).1]

/-- The native weights on the fixed observation window sum to one at every window time. -/
theorem Case.pulseWeights (x : Case plan R) (t : ℝ) (ht : t ∈ x.interval) :
    (∑ k : x.pulses, x.weight k.1 t) = 1 := by
  classical
  have hΛ : 1 ≤ x.c.D.Λ := by
    have := (Comparison.weakPassageInstance_base x.c).1; omega
  have hτ := Construction.Stream.ocTau_pos (α := x.c.D.α) (q := x.c.D.q)
    (m := x.i) hΛ
  rw [Finset.sum_coe_sort x.pulses (fun k : ℤ => x.weight k t)]
  rw [Finset.sum_congr rfl fun k hk => x.pulseWeight k
    (CycleComparison.LiftSetting.obsPulse_odd hk) t]
  refine CascadeInvariants.sum_ocCutoff_eq_one hτ x.pulses
    (fun _ hk => CycleComparison.LiftSetting.obsPulse_odd hk) t ?_
  intro k hk hne
  exact obsPulses_time_subset x.c.D.α x.c.D.q x.c.D.Λ x.i hτ ht
    (mem_obsPulses_time x.c.D.α x.c.D.q x.c.D.Λ x.i hτ hk
      (mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hne))

/-- Gluing a source over the instantaneous pulses equals the fixed observation-window sum. -/
theorem Case.sourceEulerFixed (x : Case plan R) (s : WeakSource (x.c.stage x.i))
    (t : ℝ) (ht : t ∈ x.interval) (f : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2) :
    x.sourceEulerOf s t f y j =
      ∑ k ∈ x.pulses, x.weight k t *
        pushFlux (x.chart k t) (x.label k t)
          (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
            (nativeChain (x.c.stage x.i).level k)) f y j := by
  classical
  let L := fun k => s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
    (nativeChain (x.c.stage x.i).level k)
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hΛ : 1 ≤ x.c.D.Λ := by
    have := (Comparison.weakPassageInstance_base x.c).1; omega
  have hτ := Construction.Stream.ocTau_pos (α := x.c.D.α) (q := x.c.D.q)
    (m := x.i) hΛ
  have hτ' := Construction.Stream.ocTauPP_pos (α := x.c.D.α) (q := x.c.D.q)
    (m := x.i) hΛ
  have hchart (k : ℤ) : x.chart k =
      fun t y => x.c.D.flowOf (x.i - 1) t y (x.c.D.slotAnchor x.i k) := by
    funext t y
    unfold Case.chart ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k hτ']
  have hlabel (k : ℤ) : x.label k =
      fun t y => x.c.D.flowOf (x.i - 1) (x.c.D.slotAnchor x.i k) y t := by
    funext t y
    unfold Case.label ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k hτ']
  have hweight (k : ℤ) (hk : k ∈ x.pulses) :
      x.weight k t = ocCutoff x.c.D.α x.c.D.q x.c.D.Λ x.i k t :=
    x.pulseWeight k (CycleComparison.LiftSetting.obsPulse_odd hk) t
  change (∑ k ∈ ocObsPulses x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage x.i).level t t,
    ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage x.i).level k t •
      pushFlux (fun y => x.c.D.flowOf ((x.c.stage x.i).level - 1) t y
        (x.c.D.slotAnchor (x.c.stage x.i).level k))
        (fun y => x.c.D.flowOf ((x.c.stage x.i).level - 1)
          (x.c.D.slotAnchor (x.c.stage x.i).level k) y t) (L k) f y) j = _
  conv_lhs => rw [hlevel]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hwSum : (∑ k ∈ x.pulses, x.weight k t *
      pushFlux (x.chart k t) (x.label k t) (L k) f y j) =
      ∑ k ∈ x.pulses, ocCutoff x.c.D.α x.c.D.q x.c.D.Λ x.i k t *
        pushFlux (fun y => x.c.D.flowOf (x.i - 1) t y (x.c.D.slotAnchor x.i k))
          (fun y => x.c.D.flowOf (x.i - 1) (x.c.D.slotAnchor x.i k) y t) (L k) f y j := by
    exact Finset.sum_congr rfl fun k hk => by rw [hweight k hk, hchart k, hlabel k]
  rw [hwSum]
  refine Finset.sum_subset
    (Construction.Residual.Presentation.obsPulses_time_subset
      x.c.D.α x.c.D.q x.c.D.Λ x.i hτ ht) fun k hk hnot => ?_
  have ho := CycleComparison.LiftSetting.obsPulse_odd hk
  have hout : t ∉ ocPulseWindow x.c.D.α x.c.D.q x.c.D.Λ x.i k := fun h =>
    hnot (Construction.Residual.Presentation.mem_obsPulses_time
      x.c.D.α x.c.D.q x.c.D.Λ x.i hτ ho h)
  rw [WeakEntryProofs.ocCutoff_zero_off_output x.c.D.α x.c.D.q x.c.D.Λ x.i hτ k t hout, zero_mul]

/-- Re-capping preserves the entire finite set of paths. -/
def Case.pathCapEquiv (x : Case plan R) (g : ℕ) :
    StagePath (x.c.stage x.i) g ≃ StagePath (weakWindowStage x.c x.i x.lower x.upper) g where
  toFun π := π.recap
  invFun π := x.originalPath π
  left_inv π := by cases π; rfl
  right_inv π := x.originalPath_recap π

/-- The positive classical block is the finite path sum, with each path's own source field. -/
theorem Case.cePathAction (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (hg : 1 ≤ g) (v : CompIn (x.c.stage x.i).comps)
    (Dc : ℕ) (hDc : x.cap ≤ Dc)
    (a : Vec 2 → ∀ u : CompIn (x.c.stage x.i).comps, ScalarH u.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ u : CompIn (x.c.stage x.i).comps, ∑ d : Finset.Icc 2 Dc,
      cdCE x.c Dc x.i x.lower x.upper g v u d t y
        (WithLp.toLp 2 (fun I => orderedDerivative I (fun z => a z u) y)) j) =
      ∑ n ∈ Finset.Icc 2 (A.Nw + x.incomingOrder),
        ∑ᶠ π : StagePath (x.c.stage x.i) g, if π.tgt = v.1 then
          x.sourceEulerOf (.inherited [] g π n) t
            (fun z => a z ⟨π.src, (cd_stagePath_mem x.c x.i π hg).1⟩) y j else 0 := by
  classical
  let F := fun (π : StagePath (x.c.stage x.i) g) n =>
    x.sourceEulerOf (.inherited [] g π n) t
      (fun z => a z ⟨π.src, (cd_stagePath_mem x.c x.i π hg).1⟩) y j
  rw [Finset.sum_congr rfl fun u _ =>
    x.cePhysicalAction hcommon hX hZ hg u v Dc hDc (fun z => a z u)
      (contDiff_pi.mp ha u) t y j]
  have hterm (u : CompIn (x.c.stage x.i).comps) :
      (∑ᶠ b : x.inheritedIndex g u v,
        x.sourceEulerOf (.inherited [] g b.2.1 b.1.1) t (fun z => a z u) y j) =
      ∑ᶠ b : x.inheritedIndex g u v, F b.2.1 b.1.1 := by
    refine finsum_congr fun b => ?_
    have he : (⟨b.2.1.src, (cd_stagePath_mem x.c x.i b.2.1 hg).1⟩ :
        CompIn (x.c.stage x.i).comps) = u := Subtype.ext b.2.2.1
    dsimp only [F]
    rw [he]
  rw [Finset.sum_congr rfl fun u _ => hterm u, x.inheritedComponentsSum hg v F]

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
