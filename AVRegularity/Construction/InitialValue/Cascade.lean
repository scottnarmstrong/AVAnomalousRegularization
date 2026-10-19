-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.With
public import AVRegularity.Definitions.Construction.Preparation

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! A periodic `L¹` field on the unit cell is determined by its pairings with smooth periodic test
fields (smooth tests compactly supported in the open cell periodize to themselves on the cell),
and an element of `TorusHk` is determined by its value jet up to null sets. -/

namespace InitialValue

theorem isOpen_unitCube : IsOpen (AVenhance.unitCube) := by
  simpa [AVenhance.unitCube] using (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))

/-- A smooth function with topological support in the open cell agrees on the cell with its
periodization. -/
theorem perST_eq_on_cube {g : Vec 2 → ℝ} (hg : tsupport g ⊆ AVenhance.unitCube) {x : Vec 2}
    (hx : x ∈ AVenhance.unitCube) : Applications.perST (fun _ y => g y) 0 x = g x := by
  unfold Applications.perST
  rw [finsum_eq_single _ (0 : Fin 2 → ℤ)]
  · have h0 : latticeShift (0 : Fin 2 → ℤ) = 0 := by funext i; simp [latticeShift]
    simp [h0]
  · intro n hn
    by_contra hne
    have hmem : x + latticeShift n ∈ AVenhance.unitCube := hg (subset_tsupport _ hne)
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h; push Not at h; exact hn (funext h)
    have h1 := hx i (Set.mem_univ _)
    have h2 := hmem i (Set.mem_univ _)
    simp only [Pi.add_apply, latticeShift, Set.mem_Ioo] at h1 h2
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · have : (n i : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      linarith [h1.2, h2.1]
    · have : (1 : ℝ) ≤ n i := by exact_mod_cast hpos
      linarith [h1.1, h2.2]

/-- Uniqueness from smooth periodic tests. -/
theorem ae_eq_of_cellInner_eq {F G : Vec 2 → ℝ} (hF : IntegrableOn F AVenhance.unitCube)
    (hG : IntegrableOn G AVenhance.unitCube)
    (h : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      cellInner F φ = cellInner G φ) :
    F =ᵐ[volume.restrict AVenhance.unitCube] G := by
  have hH : LocallyIntegrableOn (fun x => F x - G x) AVenhance.unitCube volume :=
    (hF.sub hG).locallyIntegrableOn
  have key := isOpen_unitCube.ae_eq_zero_of_integral_contDiff_smul_eq_zero hH ?_
  · have hm : MeasurableSet AVenhance.unitCube :=
      (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => measurableSet_Ioo)
    rw [Filter.EventuallyEq, ae_restrict_iff' hm]
    filter_upwards [key] with x hx hmem
    exact sub_eq_zero.1 (hx hmem)
  intro g hgs hgc hgsup
  obtain ⟨R, hR⟩ : ∃ R, Applications.SupBdd R (fun _ y => g y) := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun _ y hy => ?_⟩
    have := hR (subset_tsupport _ hy)
    simpa using this
  set φ := Applications.perST (fun _ y => g y) 0
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have := Applications.perST_contDiff hR (hgs.comp contDiff_snd)
    exact this.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  have hφp : IsZ2Periodic φ := Applications.perST_periodic _ 0
  have hφeq : ∀ x ∈ AVenhance.unitCube, φ x = g x := fun x hx => perST_eq_on_cube hgsup hx
  have hpair := h φ hφs hφp
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hgF : IntegrableOn (fun x => g x * F x) AVenhance.unitCube :=
    hF.bdd_mul hgs.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => hC x)
  have hgG : IntegrableOn (fun x => g x * G x) AVenhance.unitCube :=
    hG.bdd_mul hgs.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => hC x)
  have hmeas : MeasurableSet AVenhance.unitCube :=
    (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => measurableSet_Ioo)
  have hcell : ∀ K : Vec 2 → ℝ, cellInner K φ = ∫ x in AVenhance.unitCube, g x * K x := by
    intro K
    unfold cellInner
    refine setIntegral_congr_fun hmeas fun x hx => ?_
    simp only [hφeq x hx, RCLike.inner_apply, conj_trivial]
  rw [hcell, hcell] at hpair
  have hzero : ∀ x ∉ AVenhance.unitCube, g x • (F x - G x) = 0 := by
    intro x hx
    have : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hgsup h))
    simp [this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp only [smul_eq_mul, mul_sub]
  rw [integral_sub hgF hgG, hpair, sub_self]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

/-- An element of `TorusHk` is determined by its value jet up to null sets. -/
theorem torusHk_ext_of_jet_ae [FiniteDimensional ℝ E] {f g : TorusHk K E}
    (hbase : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      g.toFunction.jet (valueIndex2 K)) : f = g := by
  have hall := orderedWeakJet_unique isOpen_unitCube f.toFunction.hasPeriodicWeakJet.2.1
    g.toFunction.hasPeriodicWeakJet.2.1
    f.toFunction.hasPeriodicWeakJet.hasWeakJetOn_cell
    g.toFunction.hasPeriodicWeakJet.hasWeakJetOn_cell hbase
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (periodicJetRepresentative_ae f.val a).symm.trans
    ((hall a).trans (periodicJetRepresentative_ae g.val a))

/-- The jets of an element of `TorusHk` are integrable on the cell. -/
theorem torusHk_integrableOn_jet (f : TorusHk K E) (a : JetIndex2 K) :
    IntegrableOn (f.toFunction.jet a) AVenhance.unitCube := by
  have hI : Integrable (fun x => (f.val a : Vec 2 → E) x)
      (volume.restrict AVenhance.unitCube) := by
    have : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      have hsub : AVenhance.unitCube ⊆ Set.Icc (0 : Vec 2) 1 := fun x hx =>
        ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩
      exact (measure_mono hsub).trans_lt measure_Icc_lt_top
    exact (Lp.memLp (f.val a)).integrable (by norm_num)
  exact hI.congr (periodicJetRepresentative_ae f.val a).symm

end InitialValue

end AVRegularity
end

section
namespace AVRegularity

/-! Structural invariants of cascade stages: every birth of a component of a stage of level `i`
happened at a scale at least `i` (the seed has no births; a passage `i → i-1` records births at
scale `i - 1`), and the retained components have grade at most `H`. Hence at the passage from a
stage of level `m ≥ 1` its own components are their own parents, carry the empty word, and are
retained. -/

namespace InitialValue

variable {D : OCData} {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem mem_succExtComps {m : ℕ} {A : Finset WordLetter} {J : ℕ} {S : Finset Comp} {c : Comp}
    (hc : c ∈ succExtComps m A J S) :
    c ∈ S ∨ ∃ v ∈ S, ∃ t, c = succComp m v t := by
  unfold succExtComps at hc
  rcases Finset.mem_union.1 hc with h | h
  · exact Or.inl h
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
    exact Or.inr ⟨x.1, (Finset.mem_product.1 hx).1, x.2, rfl⟩

/-- The cascade invariant. -/
theorem cascade_invariant {P : ProvParams} {Mn : SuccMenu} {seed : GenStage D hr Dm b j₀}
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    {G : GenStage D hr Dm b j₀} (hG : IsCascadeStage D P Mn seed G) :
    ∀ c ∈ G.comps, (∀ e ∈ c.births, G.level ≤ e.scale) ∧ compGrade c ≤ Mn.H := by
  induction hG with
  | seed =>
    intro c hc
    have h := hseed ⟨c, hc⟩
    simp only at h
    simp [h, compGrade]
  | @step G G' _ hsucc ih =>
    intro c hc
    have hc' : c ∈ G'.comps.filter (IsRetained G.level Mn.H Mn.J) := hc
    obtain ⟨hcG', hret⟩ := Finset.mem_filter.1 hc'
    refine ⟨?_, hret.1⟩
    have hlev : (G'.retained G.level Mn.H Mn.J).level = G.level - 1 := hsucc.2.1
    rw [hlev]
    rw [hsucc.2.2.1] at hcG'
    rcases mem_succExtComps hcG' with hcG | ⟨v, hv, t, rfl⟩
    · intro e he; exact (Nat.sub_le _ _).trans ((ih c hcG).1 e he)
    · unfold succComp
      split_ifs with ht
      · intro e he; exact (Nat.sub_le _ _).trans ((ih v hv).1 e he)
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact le_rfl
        · exact (Nat.sub_le _ _).trans ((ih v hv).1 e he)

theorem compParent_eq_self {m : ℕ} (hm : 1 ≤ m) {c : Comp} (hc : ∀ e ∈ c.births, m ≤ e.scale) :
    compParent m c = c ∧ compWord m c = [] := by
  unfold compParent compWord
  cases h : c.births with
  | nil => simp
  | cons e rest =>
    have he : m ≤ e.scale := hc e (by rw [h]; exact List.mem_cons_self)
    have hne : e.scale ≠ m - 1 := by omega
    simp [hne]

end InitialValue

end AVRegularity
end
