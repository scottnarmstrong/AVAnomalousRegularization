-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.FullX
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.EntryWeak.PrimitiveShearWindowBound
public import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.Proofs.GenSem.CoeffArr.Mean

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.PathDecomp

/-! The stage as a branching family: the identities of `G.fam` with their maps, and as step data
their maximal orders and their flux fields in the lift variables `(c t, λ X, z)` (`liftEdges`).
The lift operator data of the Hilbert fiber and of the scalar path families have the source fluxes
of the stage family and of the chain families of the path step data. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The step data of an identity of the stage, in the lift variables. -/
def stageDat (G : GenStage D hr Dm b j₀) (c₀ lam : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (v u : CompIn G.comps) (γ : G.fam.Γ v u) : StepDat :=
  ((G.fam.identity v u γ).maxOrder, fun d α t X z =>
    if d ≤ Dm then G.fam.flux p c v u γ d α (c₀ * t) (lam • X) z else 0)

/-- The stage as a branching family. -/
def stageFam (G : GenStage D hr Dm b j₀) (c₀ lam : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) : FamData (CompIn G.comps) (fun v => hr v.1.root) where
  Γ := G.fam.Γ
  fΓ _ _ := inferInstance
  map v u γ := (G.fam.identity v u γ).map
  dat := stageDat G c₀ lam p c

/-- The step data along a stage path. -/
def pathDat (G : GenStage D hr Dm b j₀) (c₀ lam : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) {h : ℕ} (σ : StagePath G h) : Fin h → StepDat :=
  fun i => stageDat G c₀ lam p c (σ.step i).1 (σ.step i).2.1 (σ.step i).2.2

theorem list_sum_map_filterMap {α β M : Type*} [AddCommMonoid M] (l : List α) (φ : α → Option β)
    (ψ : β → M) :
    ((l.filterMap φ).map ψ).sum = (l.map fun a => (φ a).elim 0 ψ).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases h : φ a <;> simp [h, ih]

/-- **The fiber has the source flux of the stage family.** -/
theorem hasFamFlux_fiber [∀ r, FiniteDimensional ℝ (hr r)] (G : GenStage D hr Dm b j₀) (m : ℕ)
    (k : ℤ) (A : RealChain) (ρ : ℝ) (p : OddSlot) (c : StageCtx D b j₀ G.level p) :
    HasFamFlux (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c))
      (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c) := by
  classical
  intro η ε t Φ κ X z v
  simp only [sourceFlux, familyLiftData, liftEdges, ChartedFamily.fiber, List.map_map]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  rw [list_sum_map_filterMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have hdD : d.1 ≤ Dm := (Finset.mem_Icc.mp d.2).2
  by_cases hd : d.1 ≤ (G.fam.identity v u γ).maxOrder
  · simp [hd, hdD, stageFam, stageDat]
  · simp [hd, stageFam, stageDat]

/-- **A path family has the source flux of the chain family of its step data.** -/
theorem hasFamFlux_pathEdges [∀ r, FiniteDimensional ℝ (hr r)] (G : GenStage D hr Dm b j₀)
    (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ) (p : OddSlot) (c : StageCtx D b j₀ G.level p) {h : ℕ}
    (σ : StagePath G h) :
    HasFamFlux (familyLiftData (ι := Fin (h + 1)) D m k A ρ (pathEdges G σ p c))
      (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)) := by
  classical
  intro η ε t Φ κ X z v
  simp only [sourceFlux, familyLiftData, liftEdges, pathEdges]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  have hdD : d.1 ≤ Dm := (Finset.mem_Icc.mp d.2).2
  by_cases hvu : (v : ℕ) = u + 1 ∧ (u : ℕ) < h
  · have e : ∑ γ : (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)).Γ v u,
        (if d.1 ≤ ((chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)).dat v u γ).1
          then ∑ α : DerivativeWord2 (d.1 - 1),
            (((chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)).dat v u γ).2 d.1
              α t X z κ) • (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)).map
                v u γ (dEpsWord η ε α Φ X z u)
          else 0) =
        if d.1 ≤ (G.fam.identity _ _ (σ.step ⟨u, hvu.2⟩).2.2).maxOrder then
          ∑ α : DerivativeWord2 (d.1 - 1),
            G.fam.flux p c _ _ (σ.step ⟨u, hvu.2⟩).2.2 d.1 α (D.cellScaleSq m * t)
              ((ρ / D.eps (m - 1)) • X) z κ • dEpsWord η ε α Φ X z u
        else 0 := by
      have : Unique ((chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)).Γ v u) :=
        ⟨⟨⟨hvu.1⟩⟩, fun _ => rfl⟩
      rw [Fintype.sum_unique]
      simp [chainFam, pathDat, stageDat, hdD]
    rw [e]
    by_cases hd : d.1 ≤ (G.fam.identity _ _ (σ.step ⟨u, hvu.2⟩).2.2).maxOrder
    · simp [hvu, hd]
    · simp [hvu, hd]
  · have : IsEmpty ((chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ)).Γ v u) := by
      refine ⟨fun γ => hvu ⟨γ.down, ?_⟩⟩
      have := γ.down; have := v.isLt; omega
    simp [hvu]

end AVRegularity.Providers.PathDecomp
end

section
open Homogenization AVRegularity.Sobolev AVRegularity
namespace AVRegularity.Providers.PathDecomp

/-! Walks of the stage family are the stage paths.

A walk of the stage family is read off as the array of its steps (`stageSteps`); this is a
bijection onto the joined step arrays with prescribed source and target, carrying the step data of
the walk to the step data of the path and the composite map of the walk to the root path map of the
path. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  (G : GenStage D hr Dm b j₀) (c₀ lam : ℝ) (p : OddSlot) (c : StageCtx D b j₀ G.level p)

/-- The array of steps of a walk of the stage family (first step first). -/
def stageSteps : ∀ {g : ℕ} {w v : CompIn G.comps}, (stageFam G c₀ lam p c).Walk g w v →
    Fin g → Σ (v' u' : CompIn G.comps), G.fam.Γ v' u'
  | 0, _, _, _ => Fin.elim0
  | _ + 1, _, v, ⟨u, q, γ⟩ => Fin.snoc (α := fun _ => Σ (v' u' : CompIn G.comps), G.fam.Γ v' u')
      (stageSteps q) ⟨v, u, γ⟩

variable {G c₀ lam p c}

theorem stageSteps_succ_last {g : ℕ} {w u v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w u) (γ : G.fam.Γ v u) :
    stageSteps G c₀ lam p c (g := g + 1) (⟨u, q, γ⟩ : (stageFam G c₀ lam p c).Walk (g + 1) w v)
      (Fin.last g) = ⟨v, u, γ⟩ :=
  Fin.snoc_last (α := fun _ => Σ (v' u' : CompIn G.comps), G.fam.Γ v' u') _ _

theorem stageSteps_succ_castSucc {g : ℕ} {w u v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w u) (γ : G.fam.Γ v u) (i : Fin g) :
    stageSteps G c₀ lam p c (g := g + 1) (⟨u, q, γ⟩ : (stageFam G c₀ lam p c).Walk (g + 1) w v)
      i.castSucc = stageSteps G c₀ lam p c q i :=
  Fin.snoc_castSucc (α := fun _ => Σ (v' u' : CompIn G.comps), G.fam.Γ v' u') _ _ _

/-- The last step of a nonempty walk ends at its target. -/
theorem stageSteps_tgt : ∀ {g : ℕ} {w v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w v) (hg : 0 < g),
    (stageSteps G c₀ lam p c q ⟨g - 1, by omega⟩).1 = v
  | 0, _, _, _, hg => by omega
  | g + 1, _, v, ⟨u, q, γ⟩, _ => by
      have e : (⟨g + 1 - 1, by omega⟩ : Fin (g + 1)) = Fin.last g := by ext; simp
      simp only [stageSteps]
      rw [e, Fin.snoc_last]

theorem stageSteps_joined : ∀ {g : ℕ} {w v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w v) (i : ℕ) (hi : i + 1 < g),
    (stageSteps G c₀ lam p c q ⟨i + 1, hi⟩).2.1 = (stageSteps G c₀ lam p c q ⟨i, by omega⟩).1
  | 0, _, _, _, _, hi => by omega
  | g + 1, _, v, ⟨u, q, γ⟩, i, hi => by
      by_cases h1 : i + 1 < g
      · have := stageSteps_joined q i h1
        have e1 : (⟨i + 1, hi⟩ : Fin (g + 1)) = Fin.castSucc ⟨i + 1, h1⟩ := rfl
        have e2 : (⟨i, by omega⟩ : Fin (g + 1)) = Fin.castSucc ⟨i, by omega⟩ := rfl
        simp only [stageSteps]
        rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact this
      · have hi' : i = g - 1 := by omega
        have hg : 0 < g := by omega
        have e1 : (⟨i + 1, hi⟩ : Fin (g + 1)) = Fin.last g := by ext; simp; omega
        have e2 : (⟨i, by omega⟩ : Fin (g + 1)) = Fin.castSucc ⟨g - 1, by omega⟩ := by
          ext; simp; omega
        simp only [stageSteps]
        rw [e1, e2, Fin.snoc_last, Fin.snoc_castSucc]
        subst hi'
        exact (stageSteps_tgt q hg).symm

theorem stageSteps_src : ∀ {g : ℕ} {w v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w v) (hg : 0 < g),
    (stageSteps G c₀ lam p c q ⟨0, hg⟩).2.1 = w
  | 0, _, _, _, hg => by omega
  | g + 1, w, v, ⟨u, q, γ⟩, _ => by
      by_cases h0 : g = 0
      · subst h0
        obtain ⟨h⟩ := q
        have e : (⟨0, by omega⟩ : Fin 1) = Fin.last 0 := rfl
        simp only [stageSteps]
        rw [e, Fin.snoc_last]
        exact h.symm
      · have e : (⟨0, by omega⟩ : Fin (g + 1)) = Fin.castSucc ⟨0, by omega⟩ := rfl
        simp only [stageSteps]
        rw [e, Fin.snoc_castSucc]
        exact stageSteps_src q (by omega)

theorem stageSteps_dat : ∀ {g : ℕ} {w v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w v) (i : Fin g),
    (stageFam G c₀ lam p c).walkDat q i =
      stageDat G c₀ lam p c (stageSteps G c₀ lam p c q i).1 (stageSteps G c₀ lam p c q i).2.1
        (stageSteps G c₀ lam p c q i).2.2
  | 0, _, _, _, i => i.elim0
  | g + 1, _, v, ⟨u, q, γ⟩, i => by
      refine Fin.lastCases ?_ (fun i => ?_) i
      · erw [stageSteps_succ_last]
        simp only [FamData.walkDat, Fin.snoc_last]
        rfl
      · erw [stageSteps_succ_castSucc]
        simp only [FamData.walkDat, Fin.snoc_castSucc]
        exact stageSteps_dat q i

theorem stageSteps_injective : ∀ {g : ℕ} {w v : CompIn G.comps},
    Function.Injective (stageSteps G c₀ lam p c (g := g) (w := w) (v := v))
  | 0, _, _, a, b, _ => by
      obtain ⟨a⟩ := a
      obtain ⟨b⟩ := b
      rfl
  | g + 1, w, v, ⟨u, q, γ⟩, ⟨u', q', γ'⟩, h => by
      have hl := congrFun h (Fin.last g)
      erw [stageSteps_succ_last, stageSteps_succ_last] at hl
      have h2 := eq_of_heq (Sigma.mk.inj_iff.mp hl).2
      obtain ⟨rfl, hγ⟩ := Sigma.mk.inj_iff.mp h2
      have hγ' := eq_of_heq hγ
      subst hγ'
      have hq : q = q' := by
        refine stageSteps_injective (funext fun i => ?_)
        have := congrFun h i.castSucc
        erw [stageSteps_succ_castSucc, stageSteps_succ_castSucc] at this
        exact this
      rw [hq]

/-- Every joined array of steps with the right endpoints is the array of a walk. -/
theorem exists_walk_of_joined : ∀ (g : ℕ) (st : Fin g → Σ (v' u' : CompIn G.comps), G.fam.Γ v' u')
    (_ : ∀ (i : ℕ) (hi : i + 1 < g), (st ⟨i + 1, hi⟩).2.1 = (st ⟨i, by omega⟩).1)
    (w v : CompIn G.comps) (_ : ∀ h : 0 < g, (st ⟨0, h⟩).2.1 = w)
    (_ : ∀ h : 0 < g, (st ⟨g - 1, by omega⟩).1 = v) (_ : g = 0 → w = v),
    ∃ q : (stageFam G c₀ lam p c).Walk g w v, stageSteps G c₀ lam p c q = st
  | 0, st, _, w, v, _, _, h0 => ⟨⟨h0 rfl⟩, funext fun i => i.elim0⟩
  | g + 1, st, hj, w, v, hs, ht, h0 => by
      obtain ⟨⟨v', u', γ⟩, hx⟩ : ∃ x, x = st (Fin.last g) := ⟨_, rfl⟩
      have hv : v' = v := by
        have := ht (by omega)
        have e : (⟨g + 1 - 1, by omega⟩ : Fin (g + 1)) = Fin.last g := by ext; simp
        rw [e, ← hx] at this
        exact this
      subst hv
      have hu : ∀ hg : 0 < g, (st (Fin.castSucc ⟨g - 1, by omega⟩)).1 = u' := by
        intro hg
        have := hj (g - 1) (by omega)
        have e : (⟨g - 1 + 1, by omega⟩ : Fin (g + 1)) = Fin.last g := by ext; simp; omega
        rw [e, ← hx] at this
        exact this.symm
      obtain ⟨q', hq'⟩ := exists_walk_of_joined g
        (fun i => st i.castSucc) (fun i hi => hj i (by omega)) w u'
        (fun h => hs (by omega)) (fun h => hu h) (by
          intro hg
          subst hg
          have := hs (by omega)
          have e : (⟨0, by omega⟩ : Fin (0 + 1)) = Fin.last 0 := rfl
          rw [e, ← hx] at this
          exact this.symm)
      refine ⟨⟨u', q', γ⟩, funext fun i => ?_⟩
      refine Fin.lastCases ?_ (fun i => ?_) i
      · erw [stageSteps_succ_last, hx]
      · erw [stageSteps_succ_castSucc, hq']

/-- The map of a step, with the roots of its spaces. -/
def stepMap (x : Σ (v' u' : CompIn G.comps), G.fam.Γ v' u') : Σ (a c : ℕ), hr a →L[ℝ] hr c :=
  ⟨x.2.1.1.root, x.1.1.root, (G.fam.identity _ _ x.2.2).map⟩

theorem rootPathMap_concat (r₀ : ℕ) (l : List (Σ (a c : ℕ), hr a →L[ℝ] hr c)) (a c' : ℕ)
    (f : hr a →L[ℝ] hr c') (r : ℕ) :
    rootPathMap hr r₀ (l ++ [⟨a, c', f⟩]) r =
      if h : c' = r then (h ▸ f).comp (rootPathMap hr r₀ l a) else 0 := by
  induction l generalizing r₀ with
  | nil =>
      by_cases h1 : r₀ = a <;> by_cases h2 : c' = r
      · subst h1; subst h2; simp [rootPathMap]
      · subst h1; simp [rootPathMap, h2]
      · subst h2; simp [rootPathMap, h1]
      · simp [rootPathMap, h1, h2]
  | cons x rest ih =>
      obtain ⟨a', c'', f'⟩ := x
      by_cases h1 : r₀ = a'
      · subst h1
        simp only [List.cons_append, rootPathMap, ih]
        by_cases h2 : c' = r
        · subst h2; simp [ContinuousLinearMap.comp_assoc]
        · simp [h2]
      · simp [rootPathMap, h1]

theorem stageSteps_compMap : ∀ {g : ℕ} {w v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w v),
    (stageFam G c₀ lam p c).compMap q =
      rootPathMap hr w.1.root
        (StagePath.mapList ⟨stageSteps G c₀ lam p c q, stageSteps_joined q⟩) v.1.root
  | 0, w, v, ⟨h⟩ => by
      subst h
      simp [FamData.compMap, StagePath.mapList, rootPathMap]
  | g + 1, w, v, ⟨u, q, γ⟩ => by
      have hl : StagePath.mapList
          (⟨stageSteps G c₀ lam p c (g := g + 1) (⟨u, q, γ⟩ : (stageFam G c₀ lam p c).Walk (g + 1) w v),
            stageSteps_joined _⟩ : StagePath G (g + 1)) =
          StagePath.mapList ⟨stageSteps G c₀ lam p c q, stageSteps_joined q⟩ ++
            [⟨u.1.root, v.1.root, (G.fam.identity v u γ).map⟩] := by
        unfold StagePath.mapList
        rw [List.ofFn_succ']
        simp only [List.concat_eq_append]
        congr 1
        · congr 1
          funext i
          exact congrArg stepMap (stageSteps_succ_castSucc q γ i)
        · exact congrArg (fun x => [stepMap x]) (stageSteps_succ_last q γ)
      rw [hl, rootPathMap_concat]
      simp only [dite_true]
      simp only [FamData.compMap, stageSteps_compMap q]
      rfl

theorem stage_walk_path {g : ℕ} {w v : CompIn G.comps}
    (q : (stageFam G c₀ lam p c).Walk g w v) :
    ∃ σ : StagePath G g, pathDat G c₀ lam p c σ = (stageFam G c₀ lam p c).walkDat q :=
  ⟨⟨stageSteps G c₀ lam p c q, stageSteps_joined q⟩, funext fun i => (stageSteps_dat q i).symm⟩

theorem stage_path_segment {L : ℕ} (σ : StagePath G L) (i g : ℕ) (h : i + g ≤ L) :
    ∃ σ' : StagePath G g, pathDat G c₀ lam p c σ' =
      fun j => pathDat G c₀ lam p c σ ⟨i + j.val, by omega⟩ :=
  ⟨⟨fun j => σ.step ⟨i + j.val, by omega⟩, fun j hj => σ.joined (i + j) (by omega)⟩, rfl⟩

open scoped Classical in
theorem sum_stageWalk_eq {g : ℕ} (hg : 1 ≤ g) (u v : CompIn G.comps) (ev : hr u.1.root)
    (Φ : (Fin g → StepDat) → ℝ) :
    ∑ q : (stageFam G c₀ lam p c).Walk g u v,
        Φ ((stageFam G c₀ lam p c).walkDat q) • (stageFam G c₀ lam p c).compMap q ev =
      ∑ st : Fin g → (Σ (v' u' : CompIn G.comps), G.fam.Γ v' u'),
        if hj : ∀ (i : ℕ) (hi : i + 1 < g), (st ⟨i + 1, hi⟩).2.1 = (st ⟨i, by omega⟩).1 then
          if (StagePath.src ⟨st, hj⟩ = u.1 ∧ StagePath.tgt ⟨st, hj⟩ = v.1) then
            Φ (pathDat G c₀ lam p c ⟨st, hj⟩) •
              rootPathMap hr u.1.root (StagePath.mapList ⟨st, hj⟩) v.1.root ev
          else 0
        else 0 := by
  refine Fintype.sum_of_injective (stageSteps G c₀ lam p c) stageSteps_injective _ _ ?_ ?_
  · intro st hst
    split_ifs with hj hst2
    · exfalso
      refine hst ?_
      have hg' : 0 < g := hg
      obtain ⟨q, hq⟩ := exists_walk_of_joined (c₀ := c₀) (lam := lam) (p := p) (c := c) g st hj u v
        (fun h => by
          have := hst2.1
          simp only [StagePath.src, h, dite_true] at this
          exact Subtype.ext this)
        (fun h => by
          have := hst2.2
          simp only [StagePath.tgt, h, dite_true] at this
          exact Subtype.ext this)
        (fun h => by omega)
      exact ⟨q, hq⟩
    · rfl
    · rfl
  · intro q
    have hj := stageSteps_joined q
    have hs : StagePath.src (⟨stageSteps G c₀ lam p c q, hj⟩ : StagePath G g) = u.1 := by
      simp only [StagePath.src, show 0 < g by omega, dite_true]
      exact congrArg Subtype.val (stageSteps_src q (by omega))
    have ht : StagePath.tgt (⟨stageSteps G c₀ lam p c q, hj⟩ : StagePath G g) = v.1 := by
      simp only [StagePath.tgt, show 0 < g by omega, dite_true]
      exact congrArg Subtype.val (stageSteps_tgt q (by omega))
    rw [stageSteps_compMap q]
    split_ifs with h2
    · have : (stageFam G c₀ lam p c).walkDat q =
          pathDat G c₀ lam p c (⟨stageSteps G c₀ lam p c q, hj⟩ : StagePath G g) :=
        funext fun i => stageSteps_dat q i
      rw [this]
    · exact absurd ⟨hs, ht⟩ h2

end AVRegularity.Providers.PathDecomp
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Uniqueness
open AVRegularity.CycleEvolution AVRegularity.InitialLayer AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers.PathDecomp

/-! Linear algebra of cell field inverses and lift sequences.

* `isCellFieldInverse_clm`: a cell field inverse of class `C¹` composed with a continuous linear
  map is the cell field inverse of the composed source;
* `isCellFieldInverse_sum_smul`: finite superposition of scalar cell field inverses along fixed
  vectors;
* `coeff_eq_of_apply_eq_single`: symmetric word arrays that act identically on the single-component
  smooth test fields `Pi.single w (g₀ • e)` agree. -/

section Cell

local instance cellSuperProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The zero trajectory is a cell solution with zero data on any interval. -/
theorem cellSolution_zero (I : Set ℝ) (hI : I.OrdConnected) (C : CellCoefficients) :
    IsCellSolution I C (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) := by
  refine ⟨hI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Filter.Eventually.of_forall (fun t => ?_)
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · intro n x; rfl
    · exact MemLp.zero
    · intro j w i e φ _ _ _
      simp
  · intro t _
    refine ⟨?_, fun n x => rfl⟩
    exact MemLp.zero
  · intro a
    exact aestronglyMeasurable_const
  · intro t₀ _
    simp only [cellValue, sub_self, enorm_zero]
    simpa using tendsto_const_nhds
  · intro a _ b _
    have h0 : cellGradient (fun (_ : JetIndex2 1) (_ : Vec 2) => (0 : ℂ)) = fun _ => 0 := by
      funext x; ext k; simp [cellGradient, cellGradComp]
    simp [h0, cellL2Norm]
  · intro s _ t _ _ ψ
    unfold CellWeakIdentity
    simp [cellValue, cellGradComp]

/-- Finite sums of cell solutions with zero vector source. -/
theorem cellSolution_finset_sum {κ : Type*} {I : Set ℝ} (hI : I.OrdConnected)
    (C : CellCoefficients) (s : Finset κ) (src : κ → ℝ → Vec 2 → ℂ)
    (D : κ → ℝ → RawJet2 1 ℂ)
    (h : ∀ i ∈ s, IsCellSolution I C (src i) (fun _ _ => 0) (D i)) :
    IsCellSolution I C (∑ i ∈ s, src i) (fun _ _ => 0) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := cellSolution_zero I hI C
    rw [Finset.sum_empty, Finset.sum_empty]
    exact this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have := cellSolution_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have e0 : ((fun _ _ => 0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) + fun _ _ => 0) =
        fun _ _ => 0 := by
      funext _ _; simp
    rw [e0] at this
    exact this

/-- The value jet of a field is linear in the field. -/
theorem cellValue_cellJetOfField_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (ℓ : F →L[ℝ] ℝ)
    (c : ℝ → Vec 2 → E) (t : ℝ) :
    cellValue (cellJetOfField ℓ (fun t z => L (c t z))) t =
      cellValue (cellJetOfField (ℓ.comp L) c) t := by
  funext x
  simp [cellValue, cellJetOfField, valueIndex2, valueIndex]

/-- Energy-norm finiteness on `Icc t₀ t₁` from the solution property. -/
theorem cellEnergyNorm_Icc_lt_top {t₀ t₁ : ℝ} {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc t₀ t₁) C src F D) : cellEnergyNorm (Icc t₀ t₁) D < ⊤ := by
  by_cases hab : t₀ ≤ t₁
  · exact cellSolution_finite_energyNorm hab h
  · rw [Icc_eq_empty (by simpa using hab)]
    simp [cellEnergyNorm, cellUlNorm]

/-- The `fderiv`-jet of a field composed with a continuous linear map, for differentiable
fields, is the jet of the composed functional. -/
theorem cellJetOfField_clm_of_differentiable {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (ℓ : F →L[ℝ] ℝ)
    (c : ℝ → Vec 2 → E) (t : ℝ) (hd : Differentiable ℝ (c t)) :
    cellJetOfField ℓ (fun t z => L (c t z)) t = cellJetOfField (ℓ.comp L) c t := by
  funext a x
  simp only [cellJetOfField]
  split_ifs with h0
  · have : fderiv ℝ (fun z => L (c t z)) x = L.comp (fderiv ℝ (c t) x) :=
      (L.hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv
    simp [this]
  · simp

theorem isCellFieldInverse_clm {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {sZ : ℕ} (hsZ : 1 ≤ sZ) {t₀ t₁ : ℝ} {c₀ : Vec 2 → E}
    {g c : ℝ → Vec 2 → E} (L : E →L[ℝ] F)
    (h : IsCellFieldInverse G v sZ t₀ t₁ c₀ g c) :
    IsCellFieldInverse G v sZ t₀ t₁ (fun x => L (c₀ x)) (fun t z => L (g t z))
      (fun t z => L (c t z)) := by
  refine ⟨fun t ht => L.contDiff.comp (h.1 t ht), fun ℓ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.2 (ℓ.comp L)
  have hJ : ∀ t ∈ Icc t₀ t₁, cellJetOfField (ℓ.comp L) c t =
      cellJetOfField ℓ (fun t z => L (c t z)) t := fun t ht =>
    (cellJetOfField_clm_of_differentiable L ℓ c t
      ((h.1 t ht).differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hsZ))).symm
  have h1' := cellSolution_congr_jet measurableSet_Icc hJ h1
  refine ⟨h1', fun t ht => ?_, ?_, cellEnergyNorm_Icc_lt_top h1'⟩
  · rw [cellValue_cellJetOfField_clm]; exact h2 t ht
  · rw [cellValue_cellJetOfField_clm]; exact h3

theorem isCellFieldInverse_sum_smul {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} (hsZ : 1 ≤ sZ) {t₀ t₁ : ℝ} {κ : Type*} (s : Finset κ)
    (g c : κ → ℝ → Vec 2 → ℝ) (e : κ → E)
    (h : ∀ i ∈ s, IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) (g i) (c i)) :
    IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) (fun t z => ∑ i ∈ s, g i t z • e i)
      (fun t z => ∑ i ∈ s, c i t z • e i) := by
  classical
  have hdiff : ∀ i ∈ s, ∀ t ∈ Icc t₀ t₁, Differentiable ℝ (c i t) := fun i hi t ht =>
    ((h i hi).1 t ht).differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hsZ)
  refine ⟨fun t ht => ContDiff.sum fun i hi => ((h i hi).1 t ht).smul contDiff_const,
    fun ℓ => ?_⟩
  let ℓi : κ → ℝ →L[ℝ] ℝ := fun i => ℓ (e i) • ContinuousLinearMap.id ℝ ℝ
  have hi : ∀ i ∈ s, _ := fun i hi => (h i hi).2 (ℓi i)
  have hsol := cellSolution_finset_sum (ordConnected_Icc (a := t₀) (b := t₁))
    (⟨fun t _ => G t, v, 0, 0⟩ : CellCoefficients) s
    (fun i t x => ((ℓi i (g i t x) : ℝ) : ℂ)) (fun i => cellJetOfField (ℓi i) (c i))
    (fun i hi' => (hi i hi').1)
  have hsrc : (fun t x => ((ℓ (∑ i ∈ s, g i t x • e i) : ℝ) : ℂ)) =
      ∑ i ∈ s, fun t x => ((ℓi i (g i t x) : ℝ) : ℂ) := by
    funext t x
    simp [ℓi, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hval : ∀ t, cellValue (cellJetOfField ℓ (fun t z => ∑ i ∈ s, c i t z • e i)) t =
      ∑ i ∈ s, cellValue (cellJetOfField (ℓi i) (c i)) t := by
    intro t
    funext x
    simp [cellValue, cellJetOfField, valueIndex2, valueIndex, ℓi, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hJ : ∀ t ∈ Icc t₀ t₁, (∑ i ∈ s, cellJetOfField (ℓi i) (c i)) t =
      cellJetOfField ℓ (fun t z => ∑ i ∈ s, c i t z • e i) t := by
    intro t ht
    funext a x
    simp only [cellJetOfField, Finset.sum_apply]
    split_ifs with h0
    · have hf : fderiv ℝ (fun z => ∑ i ∈ s, c i t z • e i) x =
          ∑ i ∈ s, (fderiv ℝ (c i t) x).smulRight (e i) := by
        rw [fderiv_fun_sum (fun i hi' => ((hdiff i hi' t ht) x).smul_const (e i))]
        exact Finset.sum_congr rfl fun i hi' => fderiv_smul_const (hdiff i hi' t ht x) (e i)
      simp [hf, ℓi, map_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · simp [ℓi, map_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hsol' : IsCellSolution (Icc t₀ t₁) ⟨fun t _ => G t, v, 0, 0⟩
      (fun t x => ((ℓ (∑ i ∈ s, g i t x • e i) : ℝ) : ℂ)) (fun _ _ => 0)
      (cellJetOfField ℓ (fun t z => ∑ i ∈ s, c i t z • e i)) := by
    rw [hsrc]
    exact cellSolution_congr_jet measurableSet_Icc hJ hsol
  refine ⟨hsol', fun t ht => ?_, ?_, cellEnergyNorm_Icc_lt_top hsol'⟩
  · have hint : ∀ i ∈ s, Integrable (fun x => cellValue (cellJetOfField (ℓi i) (c i)) t x)
        (volume.restrict AVenhance.unitCube) := fun i hi' =>
      ((hi i hi').1.2.2.1 t ht).1.integrable (by norm_num)
    rw [hval t]
    unfold cellMean
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ hint]
    exact Finset.sum_eq_zero fun i hi' => (hi i hi').2.1 t ht
  · rw [hval t₀]
    have hae : ∀ i ∈ s, cellValue (cellJetOfField (ℓi i) (c i)) t₀ =ᵐ[
        volume.restrict AVenhance.unitCube] fun _ => 0 := fun i hi' => by
      simpa using (hi i hi').2.2.1
    have := (Filter.eventually_all_finset s).2 hae
    filter_upwards [this] with x hx
    simp [Finset.sum_apply, Finset.sum_eq_zero hx]

end Cell

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem coeff_eq_of_apply_eq_single (n : ℕ) (A A' : LiftCoeff ι h)
    (hs : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), A m (α ∘ σ) = A m α)
    (hs' : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), A' m (α ∘ σ) = A' m α)
    (t : ℝ) (X z : Vec 2)
    (hap : ∀ (w : ι) (e : h w) (g₀ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g₀ →
      liftApply n A (fun _ Y => Pi.single w (g₀ Y • e)) t X z =
        liftApply n A' (fun _ Y => Pi.single w (g₀ Y • e)) t X z) :
    ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, A m α t X z v u = A' m α t X z v u := by
  intro m hm α₀ v u₀
  let Δ : ∀ m', DerivativeWord2 m' → (h u₀ →L[ℝ] h v) :=
    fun m' α => A m' α t X z v u₀ - A' m' α t X z v u₀
  suffices H : ∀ w₀ : h u₀, Δ m α₀ w₀ = 0 by
    have hΔ : Δ m α₀ = 0 := ContinuousLinearMap.ext H
    exact sub_eq_zero.mp hΔ
  intro w₀
  have key : ∀ s r : ℝ, ∑ m' ∈ Finset.range (n + 1),
      s ^ m' • ∑ α : DerivativeWord2 m', r ^ onesCount α • Δ m' α w₀ = 0 := by
    intro s r
    have hcd : ContDiff ℝ (⊤ : ℕ∞)
        (fun Y : Vec 2 => Real.exp (∑ i, (![s, s * r] : Fin 2 → ℝ) i * Y i)) := by
      refine Real.contDiff_exp.comp ?_
      refine ContDiff.sum (fun i _ => ?_)
      exact contDiff_const.mul (contDiff_apply ℝ ℝ i)
    have hexp : (fun (_ : ℝ) (Y : Vec 2) => (Pi.single u₀
        (Real.exp (∑ i, (![s, s * r] : Fin 2 → ℝ) i * Y i) • w₀) : ∀ i, h i)) =
        fun _ => expField ![s, s * r] (Pi.single u₀ w₀ : ∀ i, h i) := by
      funext _ Y
      simp only [expField]
      rw [Pi.single_smul]
    have h0 := hap u₀ w₀ _ hcd
    rw [hexp] at h0
    have h1 := congrFun h0 v
    rw [liftApply_expField, liftApply_expField] at h1
    have h3 := smul_right_injective _ (Real.exp_pos (∑ i, (![s, s * r] : Fin 2 → ℝ) i * X i)).ne' h1
    have h4 := sub_eq_zero.mpr h3
    rw [← Finset.sum_sub_distrib] at h4
    rw [← h4]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [prod_expDirection, ← smul_sub, smul_smul]
    simp only [Δ, sub_apply, smul_sub]
  have hA : ∀ r : ℝ, ∀ m' ≤ n, ∑ α : DerivativeWord2 m', r ^ onesCount α • Δ m' α w₀ = 0 := by
    intro r
    exact poly_coeff_zero_vec n (fun m' => ∑ α : DerivativeWord2 m', r ^ onesCount α • Δ m' α w₀)
      (fun x => key x r)
  have hB : ∀ k ≤ m, ∑ α ∈ Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = k),
      Δ m α w₀ = 0 := by
    have hfib : ∀ r : ℝ, ∑ k ∈ Finset.range (m + 1), r ^ k •
        ∑ α ∈ Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = k), Δ m α w₀ = 0 := by
      intro r
      rw [← hA r m hm]
      rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (DerivativeWord2 m)))
        (t := Finset.range (m + 1)) (g := fun α => onesCount α)
        (fun α _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (onesCount_le α)))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun α hα => ?_)
      rw [(Finset.mem_filter.mp hα).2]
    exact poly_coeff_zero_vec m _ hfib
  have hC := hB (onesCount α₀) (onesCount_le α₀)
  have hconst : ∀ α ∈ Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = onesCount α₀),
      Δ m α w₀ = Δ m α₀ w₀ := by
    intro α hα
    obtain ⟨σ, hσ⟩ := exists_perm_of_onesCount_eq α α₀ (Finset.mem_filter.mp hα).2
    simp only [Δ, sub_apply]
    rw [hσ, hs m α₀ σ, hs' m α₀ σ]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const] at hC
  have hpos : (Finset.univ.filter (fun α : DerivativeWord2 m => onesCount α = onesCount α₀)).card ≠ 0 := by
    apply Finset.card_ne_zero_of_mem (a := α₀)
    simp
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hC
  exact (smul_eq_zero.mp hC).resolve_left (by exact_mod_cast hpos)

end AVRegularity.Providers.PathDecomp
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.PathDecomp

/-! The uniqueness step of the path decomposition.

For a branching family `F` with operator data `Q`, a lift sequence `Cc` of `Q`, and lift
sequences `Lift g cd` of the chain families of the step data `cd` that arise from walks, put
`T g cd = topArr (Lift g cd)`. If `Cc` agrees with the path-candidate array `cand F T` below the
pair `(g, n)`, and each chain lift agrees with its own path-candidate array below `(g, n)`, then
`Cc` agrees with `cand F T` at `(g, n)`: the candidate value is the superposition of the chain
values (each a cell inverse of its chain source), the candidate source is the superposition of
the chain sources (`liftCellSource_cand`, `chain_liftCellSource_last`), and the cell inverse is
unique on the window. -/

section
open AVRegularity.Uniqueness

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)] [∀ i, FiniteDimensional ℝ (hs i)]

open Classical in
/-- The top arrays of the arising chain lifts (zero elsewhere). -/
def topOf (Lift : ∀ g, (Fin g → StepDat) → ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ))
    (Arise : ∀ g, (Fin g → StepDat) → Prop) : (g : ℕ) → (Fin g → StepDat) → SArr :=
  fun g cd => if Arise g cd then topArr (Lift g cd) else 0

/-- The context of the explicit formulas built from operator data. -/
def ctxOf {Dm : ℕ} (Q : LiftOperatorData ι hs Dm) (g₀ : Vec 2 → ℝ)
    (T : (g : ℕ) → (Fin g → StepDat) → SArr) (t : ℝ) : Ctx :=
  ⟨Q.η, Q.G, Q.v, Dm, g₀, T, t⟩

/-- The hypotheses of the uniqueness step. -/
structure StepHyp {Dm : ℕ} (F : FamData ι hs) (Q : LiftOperatorData ι hs Dm)
    (Lift : ∀ g, (Fin g → StepDat) → ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ))
    (Qc : ∀ g, (Fin g → StepDat) → LiftOperatorData (Fin (g + 1)) (fun _ => ℝ) Dm)
    (Arise : ∀ g, (Fin g → StepDat) → Prop) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N r Hb : ℕ) : Prop where
  hQ : HasFamFlux Q F
  hab : t₀ ≤ t₁
  hW : ∀ X, ∃ lo A Mv : ℝ, WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv
  hQc : ∀ g cd, Arise g cd → HasFamFlux (Qc g cd) (chainFam cd)
  hη : ∀ g cd, (Qc g cd).η = Q.η
  hG : ∀ g cd, (Qc g cd).G = Q.G
  hv : ∀ g cd, (Qc g cd).v = Q.v
  hLs : ∀ g cd, Arise g cd → IsLiftSequence (Qc g cd) sX sZ t₀ t₁ N g (Lift g cd)
  hcd : ∀ g cd, Arise g cd → ∀ i, ∀ t ∈ Icc t₀ t₁, GoodDat (r + 1 + Dm) t (cd i)
  hdat : ∀ v u (γ : F.Γ v u), ∀ t ∈ Icc t₀ t₁, GoodDat (r + 1 + Dm) t (F.dat v u γ)
  hGr : ∀ t ∈ Icc t₀ t₁, ∀ a b, ContDiff ℝ ((r + 2 : ℕ) : ℕ∞) (fun X => Q.G t X a b)
  hvr : ∀ t ∈ Icc t₀ t₁, ∀ κ, GoodField (r + 2) (fun (_ z : Vec 2) => Q.v t z κ)
  hD2 : 2 ≤ Dm
  hsX : r + 1 + Dm ≤ sX
  hsZ : r + 1 + Dm ≤ sZ
  hNr : N ≤ r
  hArise : ∀ g w v (q : F.Walk g w v), g ≤ Hb → Arise g (F.walkDat q)

omit [∀ i, FiniteDimensional ℝ (hs i)] in
theorem contDiff_single_smul {w : ι} (e : hs w) {g₀ : Vec 2 → ℝ}
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y => (Pi.single w (g₀ Y • e) : ∀ i, hs i)) := by
  have : (fun Y => (Pi.single w (g₀ Y • e) : ∀ i, hs i)) =
      fun Y => ((ContinuousLinearMap.id ℝ ℝ).smulRight (Pi.single w e : ∀ i, hs i)) (g₀ Y) := by
    funext Y; simp [Pi.single_smul]
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.comp hg₀

namespace StepHyp

variable {Dm : ℕ} {F : FamData ι hs} {Q : LiftOperatorData ι hs Dm}
  {Lift : ∀ g, (Fin g → StepDat) → ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ)}
  {Qc : ∀ g, (Fin g → StepDat) → LiftOperatorData (Fin (g + 1)) (fun _ => ℝ) Dm}
  {Arise : ∀ g, (Fin g → StepDat) → Prop} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N r Hb : ℕ}

theorem topOf_of_arise {g : ℕ} {cd : Fin g → StepDat} (h : Arise g cd) :
    topOf Lift Arise g cd = topArr (Lift g cd) := by
  classical
  simp [topOf, h]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (hs i)] in
theorem goodT (S : StepHyp F Q Lift Qc Arise sX sZ t₀ t₁ N r Hb) (g₀ : Vec 2 → ℝ) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) : (ctxOf Q g₀ (topOf Lift Arise) t).GoodT (r + 1 + Dm) := by
  classical
  intro g cd k m α
  by_cases h : Arise g cd
  · simp only [ctxOf, topOf, h, ite_true, topArr]
    obtain ⟨_, _, _, _, _, h5, _⟩ := S.hLs g cd h
    have hb := ((h5 g le_rfl k m α (Fin.last g) 0 t ht).1).map_clm
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    refine ⟨(hb.contDiff_uncurry S.hsX S.hsZ), fun X n x => ?_⟩
    have := (h5 g le_rfl k m α (Fin.last g) 0 t ht).2 X n x
    simp only at this ⊢
    rw [this]
  · simp only [ctxOf, topOf, h, ite_false]
    exact GoodField.zero

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (hs i)] in
theorem goodGv (S : StepHyp F Q Lift Qc Arise sX sZ t₀ t₁ N r Hb) (g₀ : Vec 2 → ℝ)
    (T : (g : ℕ) → (Fin g → StepDat) → SArr) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    (ctxOf Q g₀ T t).GoodGv (r + 2) :=
  ⟨S.hGr t ht, S.hvr t ht⟩

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (hs i)] in
/-- The scalar chain values on `Pi.single 0 g₀` are the scalar values of the formulas. -/
theorem chainVal_eq (_S : StepHyp F Q Lift Qc Arise sX sZ t₀ t₁ N r Hb) {g₀ : Vec 2 → ℝ}
    (hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀) {g : ℕ} {cd : Fin g → StepDat} (h : Arise g cd) (k : ℕ)
    (t : ℝ) (X z : Vec 2) :
    liftApply k (Lift g cd g k) (fun _ Y => Pi.single (0 : Fin (g + 1)) (g₀ Y)) t X z (Fin.last g) =
      (ctxOf Q g₀ (topOf Lift Arise) t).valF k g cd X z := by
  rw [chain_liftApply_last _ hg₀]
  simp only [Ctx.valF, ctxOf, topOf_of_arise h, topArr]

/-- **The uniqueness step.** -/
theorem step (S : StepHyp F Q Lift Qc Arise sX sZ t₀ t₁ N r Hb) {H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (g n : ℕ)
    (hgH : g ≤ H) (hgB : g ≤ Hb)
    (IHC : ∀ g' n', (g' < g ∨ (g' = g ∧ n' < n)) →
      CoeffEq Cc (cand F (topOf Lift Arise)) t₀ t₁ g' n')
    (IHL : ∀ cd : Fin g → StepDat, Arise g cd → ∀ g' n', (g' < g ∨ (g' = g ∧ n' < n)) →
      CoeffEq (Lift g cd) (cand (chainFam cd) (topOf Lift Arise)) t₀ t₁ g' n') :
    CoeffEq Cc (cand F (topOf Lift Arise)) t₀ t₁ g n := by
  classical
  set T := topOf Lift Arise with hTdef
  -- the chain lift arrays vanish where the clauses say so
  have hTzero : ∀ (g' : ℕ) (cd : Fin g' → StepDat) k m (α : DerivativeWord2 m) t X z,
      (g' ≠ 0 ∧ k = 0 ∨ N < k ∨ k < m) → t ∈ Icc t₀ t₁ → T g' cd k m α t X z = 0 := by
    intro g' cd k m α t X z hc ht
    by_cases h : Arise g' cd
    · obtain ⟨_, h1, h2, h3, _, _, _⟩ := S.hLs g' cd h
      simp only [hTdef, topOf_of_arise h, topArr]
      rcases hc with ⟨hg, hk⟩ | hk | hk
      · subst hk; rw [h1 g' (Nat.one_le_iff_ne_zero.mpr hg) le_rfl m α t X z]; rfl
      · rw [h2 g' le_rfl k hk m α t X z]; rfl
      · rw [h3 g' le_rfl k m hk α t X z]; rfl
    · simp [hTdef, topOf, h]
  have hcandZero : ∀ k m (α : DerivativeWord2 m) t X z v u,
      (g ≠ 0 ∧ k = 0 ∨ N < k ∨ k < m) → t ∈ Icc t₀ t₁ →
      cand F T g k m α t X z v u = 0 := by
    intro k m α t X z v u hc ht
    simp only [cand]
    exact Finset.sum_eq_zero fun q _ => by rw [hTzero g _ k m α t X z hc ht, zero_smul]
  have hsymT : ∀ (g' : ℕ) (cd : Fin g' → StepDat) k m (α : DerivativeWord2 m)
      (σ : Equiv.Perm (Fin m)), T g' cd k m (α ∘ σ) = T g' cd k m α := by
    intro g' cd k m α σ
    by_cases h : Arise g' cd
    · obtain ⟨_, _, _, _, h4, _, _⟩ := S.hLs g' cd h
      funext t X z
      simp only [hTdef, topOf_of_arise h, topArr, h4 g' le_rfl k m α σ]
    · simp [hTdef, topOf, h]
  have hsymCand : ∀ k m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
      cand F T g k m (α ∘ σ) = cand F T g k m α := by
    intro k m α σ
    funext t X z v u
    simp only [cand, hsymT]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  intro t ht m α
  funext X z v u
  by_cases hn0 : n = 0
  · subst hn0
    by_cases hg0 : g = 0
    · subst hg0
      -- grade and degree zero: both arrays act as the identity
      by_cases hm : m ≤ 0
      · refine coeff_eq_of_apply_eq_single 0 (Cc 0 0) (cand F T 0 0) (h4 0 (Nat.zero_le H) 0)
          (hsymCand 0) t X z (fun w e g₀ hg₀ => ?_) m hm α v u
        rw [h0 _ (contDiff_single_smul e hg₀) t ht X z,
          show liftApply 0 (cand F T 0 0) (fun _ Y => Pi.single w (g₀ Y • e)) t X z = _ from
            liftApply_cand F (ctxOf Q g₀ T t) hg₀ e 0 0 X z]
        have hA : Arise 0 (Fin.elim0 : Fin 0 → StepDat) := by
          have := S.hArise 0 w w (⟨rfl⟩ : F.Walk 0 w w) (Nat.zero_le _)
          simpa [FamData.walkDat] using this
        have hval : (ctxOf Q g₀ T t).valF 0 0 Fin.elim0 X z = g₀ X := by
          rw [← chainVal_eq S hg₀ hA 0 t X z]
          obtain ⟨c0, _⟩ := S.hLs 0 Fin.elim0 hA
          have := congrFun (c0 (fun Y => Pi.single (0 : Fin 1) (g₀ Y))
            (by have h := contDiff_single_smul (hs := fun _ : Fin 1 => ℝ) (w := 0) (1 : ℝ) hg₀
                simpa using h) t ht X z) (Fin.last 0)
          simpa using this
        rw [Fintype.sum_sigma, Finset.sum_eq_single w]
        · have : Unique (F.Walk 0 w w) := ⟨⟨⟨rfl⟩⟩, fun q => by cases q; rfl⟩
          rw [Fintype.sum_unique]
          have hd : F.walkDat (default : F.Walk 0 w w) = Fin.elim0 := funext fun i => Fin.elim0 i
          show _ = (ctxOf Q g₀ T t).valF 0 0 (F.walkDat (default : F.Walk 0 w w)) X z •
            (Pi.single w (F.compMap (default : F.Walk 0 w w) e) : ∀ i, hs i)
          have hc : F.compMap (default : F.Walk 0 w w) e = e := rfl
          rw [hd, hval, hc, Pi.single_smul]
        · intro b _ hb
          have : IsEmpty (F.Walk 0 w b) := ⟨fun q => hb q.down.symm⟩
          exact Fintype.sum_empty _
        · intro h; exact absurd (Finset.mem_univ w) h
      · have hm' : 0 < m := by omega
        rw [h3 0 (Nat.zero_le H) 0 m hm' α t X z v u,
          hcandZero 0 m α t X z v u (Or.inr (Or.inr hm')) ht]
    · rw [h1 g (Nat.one_le_iff_ne_zero.mpr hg0) hgH m α t X z v u,
        hcandZero 0 m α t X z v u (Or.inl ⟨hg0, rfl⟩) ht]
  · by_cases hnN : N < n
    · rw [h2 g hgH n hnN m α t X z v u, hcandZero n m α t X z v u (Or.inr (Or.inl hnN)) ht]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnN' : n ≤ N := not_lt.mp hnN
      have hsZ1 : 1 ≤ sZ := by have := S.hsZ; omega
      have huniq : ∀ (w : ι) (e : hs w) (g₀ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g₀ →
          ∀ t' ∈ Icc t₀ t₁, ∀ z',
            liftApply n (Cc g n) (fun _ Y => Pi.single w (g₀ Y • e)) t' X z' =
              liftApply n (cand F T g n) (fun _ Y => Pi.single w (g₀ Y • e)) t' X z' := by
        intro w e g₀ hg₀
        have ha₀ := contDiff_single_smul e hg₀
        let b₀ : Vec 2 → Fin (g + 1) → ℝ := fun Y => Pi.single 0 (g₀ Y)
        have hb₀ : ContDiff ℝ (⊤ : ℕ∞) b₀ := by
          have h := contDiff_single_smul (hs := fun _ : Fin (g + 1) => ℝ) (w := 0) (1 : ℝ) hg₀
          simpa using h
        obtain ⟨lo, A, Mv, hWX⟩ := S.hW X
        have hc := h6 g hgH n hn1 hnN' _ ha₀ X
        let chainSrc : WalkFrom F g w → ℝ → Vec 2 → ℝ := fun p t' z' =>
          liftCellSource (Qc g (F.walkDat p.2)) (Lift g (F.walkDat p.2)) (fun _ => b₀) g n t' X z'
            (Fin.last g)
        let chainVal : WalkFrom F g w → ℝ → Vec 2 → ℝ := fun p t' z' =>
          liftApply n (Lift g (F.walkDat p.2) g n) (fun _ => b₀) t' X z' (Fin.last g)
        have hchain : ∀ p ∈ (Finset.univ : Finset (WalkFrom F g w)),
            IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁ (fun _ => 0)
              (chainSrc p) (chainVal p) := by
          intro p _
          have hA := S.hArise g w p.1 p.2 hgB
          have h := (S.hLs g _ hA).2.2.2.2.2.2 g le_rfl n hn1 hnN' b₀ hb₀ X
          rw [S.hG, S.hv] at h
          have h' := isCellFieldInverse_clm hsZ1
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (g + 1) => ℝ) (Fin.last g)) h
          simpa using h'
        have hc' := isCellFieldInverse_sum_smul hsZ1 Finset.univ chainSrc chainVal (walkVec F e)
          hchain
        have hsrc : ∀ t' ∈ Icc t₀ t₁, ∀ z',
            liftCellSource Q Cc (fun _ Y => Pi.single w (g₀ Y • e)) g n t' X z' =
              ∑ p ∈ (Finset.univ : Finset (WalkFrom F g w)), chainSrc p t' z' • walkVec F e p := by
          intro t' ht' z'
          rw [congrFun (congrFun (liftCellSource_congr Q g n hn1 IHC ht'
            (fun _ Y => Pi.single w (g₀ Y • e))) X) z']
          rw [show liftCellSource Q (cand F T) (fun _ Y => Pi.single w (g₀ Y • e)) g n t' X z' = _
            from liftCellSource_cand F Q S.hQ (ctxOf Q g₀ T t') rfl rfl rfl rfl S.hD2
              (S.goodT g₀ ht') hg₀ (S.goodGv g₀ T ht') (fun v u γ => S.hdat v u γ t' ht') e g n
              (le_trans hnN' S.hNr) X z']
          refine Finset.sum_congr rfl fun p _ => ?_
          congr 1
          have hA := S.hArise g w p.1 p.2 hgB
          have e1 := congrFun (congrFun (congrFun (liftCellSource_congr (Qc g (F.walkDat p.2)) g n
            hn1 (IHL _ hA) ht' (fun _ => b₀)) X) z') (Fin.last g)
          show _ = liftCellSource (Qc g (F.walkDat p.2)) (Lift g (F.walkDat p.2)) (fun _ => b₀) g n
            t' X z' (Fin.last g)
          rw [e1]
          exact (chain_liftCellSource_last (F.walkDat p.2) (Qc g _) (S.hQc g _ hA)
            (ctxOf Q g₀ T t') (S.hη g _).symm (S.hG g _).symm (S.hv g _).symm rfl S.hD2
            (S.goodT g₀ ht') hg₀ (S.goodGv g₀ T ht') (fun i => S.hcd g _ hA i t' ht') n
            (le_trans hnN' S.hNr) X z').symm
        have hval : ∀ t' z', liftApply n (cand F T g n) (fun _ Y => Pi.single w (g₀ Y • e)) t' X z' =
            ∑ p ∈ (Finset.univ : Finset (WalkFrom F g w)), chainVal p t' z' • walkVec F e p := by
          intro t' z'
          rw [show liftApply n (cand F T g n) (fun _ Y => Pi.single w (g₀ Y • e)) t' X z' = _ from
            liftApply_cand F (ctxOf Q g₀ T t') hg₀ e n g X z']
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [show chainVal p t' z' = _ from chainVal_eq S hg₀ (S.hArise g w p.1 p.2 hgB) n t' X z']
        have hu := cellField_unique_window S.hab hWX hsrc hc hc'
        intro t' ht' z'
        rw [hu t' ht' z', hval]
      by_cases hm : m ≤ n
      · exact coeff_eq_of_apply_eq_single n (Cc g n) (cand F T g n) (h4 g hgH n) (hsymCand n) t X z
          (fun w e g₀ hg₀ => huniq w e g₀ hg₀ t ht z) m hm α v u
      · rw [h3 g hgH n m (by omega) α t X z v u,
          hcandZero n m α t X z v u (Or.inr (Or.inr (by omega))) ht]

end StepHyp
end

/-! **The path decomposition of lift sequences.** By strong induction on `(grade, degree)`, the
lift sequence of a branching family agrees on the window with its path-candidate array built from
the top entries of the chain lifts, and so does every arising chain lift with its own. -/

section
open AVRegularity.Uniqueness

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type} [∀ i, NormedAddCommGroup (hs i)]
  [∀ i, NormedSpace ℝ (hs i)] [∀ i, FiniteDimensional ℝ (hs i)]

/-- **Path decomposition.** -/
theorem decomp {Dm : ℕ} {F : FamData ι hs} {Q : LiftOperatorData ι hs Dm}
    {Lift : ∀ g, (Fin g → StepDat) → ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ)}
    {Qc : ∀ g, (Fin g → StepDat) → LiftOperatorData (Fin (g + 1)) (fun _ => ℝ) Dm}
    {Arise : ∀ g, (Fin g → StepDat) → Prop} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N r H : ℕ}
    (hS : StepHyp F Q Lift Qc Arise sX sZ t₀ t₁ N r H)
    (hSc : ∀ L (cd : Fin L → StepDat), Arise L cd → L ≤ H →
      StepHyp (chainFam cd) (Qc L cd) Lift Qc Arise sX sZ t₀ t₁ N r L)
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) :
    ∀ g ≤ H, ∀ n, CoeffEq Cc (cand F (topOf Lift Arise)) t₀ t₁ g n := by
  set T := topOf Lift Arise
  have main : ∀ g n,
      (∀ L (cd : Fin L → StepDat), Arise L cd → L ≤ H → g ≤ L →
        CoeffEq (Lift L cd) (cand (chainFam cd) T) t₀ t₁ g n) ∧
      (g ≤ H → CoeffEq Cc (cand F T) t₀ t₁ g n) := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ihg =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    have IH : ∀ g' n', (g' < g ∨ (g' = g ∧ n' < n)) →
        (∀ L (cd : Fin L → StepDat), Arise L cd → L ≤ H → g' ≤ L →
          CoeffEq (Lift L cd) (cand (chainFam cd) T) t₀ t₁ g' n') ∧
        (g' ≤ H → CoeffEq Cc (cand F T) t₀ t₁ g' n') := by
      intro g' n' h
      rcases h with h | ⟨rfl, h⟩
      · exact ihg g' h n'
      · exact ihn n' h
    have IHL : g ≤ H → ∀ cd : Fin g → StepDat, Arise g cd → ∀ g' n',
        (g' < g ∨ (g' = g ∧ n' < n)) →
          CoeffEq (Lift g cd) (cand (chainFam cd) T) t₀ t₁ g' n' := by
      intro hgH cd hA g' n' h
      exact (IH g' n' h).1 g cd hA hgH (by rcases h with h | ⟨h, -⟩ <;> omega)
    refine ⟨fun L cd hA hLH hgL => ?_, fun hgH => ?_⟩
    · exact (hSc L cd hA hLH).step (hS.hLs L cd hA) g n hgL hgL
        (fun g' n' h => (IH g' n' h).1 L cd hA hLH (by rcases h with h | ⟨h, -⟩ <;> omega))
        (IHL (le_trans hgL hLH))
    · exact hS.step hC g n hgH hgH (fun g' n' h => (IH g' n' h).2
        (by rcases h with h | ⟨h, -⟩ <;> omega)) (IHL hgH)
  intro g hg n
  exact (main g n).2 hg
end

end AVRegularity.Providers.PathDecomp
end
