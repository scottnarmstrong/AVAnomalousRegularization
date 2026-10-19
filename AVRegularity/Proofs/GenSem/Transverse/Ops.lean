-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.BoxJoint
import AVRegularity.CycleReference.SingleModeFlux
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.CycleReference
namespace AVRegularity.Providers.GenSem

/-! Parallel direction of a pulse and invariance of the shear data under parallel shifts:
the shear velocity of the pulse `p` depends only on its
transverse coordinate `transverseIndex p`, so it is unchanged by a shift along the parallel
direction `parIdx p`; hence so are the relative displacement `relDisp` and the cell drift. -/

/-- The parallel coordinate of the pulse `p`: the one complementary to `transverseIndex p`. -/
def parIdx (p : ℤ) : Fin 2 := if p % 4 = 3 then 0 else 1

theorem parIdx_ne_transverseIndex (p : ℤ) : parIdx p ≠ transverseIndex p := by
  unfold parIdx transverseIndex
  split_ifs <;> decide

/-- Shifting along the parallel direction does not move the transverse coordinate. -/
theorem par_shift_transverse (p : ℤ) (η : Vec 2) (s : ℝ) :
    (η + s • basisVec (parIdx p)) (transverseIndex p) = η (transverseIndex p) := by
  have h := parIdx_ne_transverseIndex p
  simp [basisVec_apply, h.symm]

/-- The shear velocity of a pulse is unchanged along its parallel direction. -/
theorem ocShearVel_add_parallel (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) (c : ℝ) :
    ocShearVel α q Λ m k (y + c • basisVec (parIdx k)) = ocShearVel α q Λ m k y := by
  by_cases h1 : k % 4 = 1
  · have h3 : ¬ k % 4 = 3 := by omega
    simp only [ocShearVel_horizontal h1, parIdx, h3, ite_false]
    simp
  · by_cases h3 : k % 4 = 3
    · simp only [ocShearVel_vertical h3, parIdx, h3, ite_true]
      simp
    · have h0 : ∀ z, ocShearVel α q Λ m k z = 0 := by
        intro z
        have hψ : ocShear α q Λ m k = fun _ => 0 := by
          funext w
          rw [ocShear_sine_formula]
          simp [h1, h3]
        change AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (ocShear α q Λ m k) z) = 0
        have hg : AVenhance.spaceGrad (fun _ : Vec 2 => (0 : ℝ)) z = 0 := by
          funext i; simp [AVenhance.spaceGrad]
        rw [hψ, hg, Matrix.mulVec_zero]
      simp only [h0]

/-- The relative displacement of the pulse `p` is unchanged by a parallel shift of `θ`. -/
theorem relDisp_add_parallel (D : OCData) (i : ℕ) (p : ℤ) (u r : ℝ) (θ : Vec 2) (c : ℝ) :
    D.relDisp i p u r (θ + c • basisVec (parIdx p)) = D.relDisp i p u r θ := by
  have key : D.eps i • (θ + c • basisVec (parIdx p)) =
      D.eps i • θ + (D.eps i * c) • basisVec (parIdx p) := by rw [smul_add, smul_smul]
  unfold OCData.relDisp
  rw [key, ocShearVel_add_parallel]

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity
namespace AVRegularity.Providers.GenSem

/-! Parallel shifts of the child phases of a real chain.

`ParEq ch ch'`: `ch'` is obtained from `ch` by shifting the phase of each child independently, by
an arbitrary real amount, along the parallel direction of the pulse of that child. The child of
level `baseLevel + 1 + k` pairs with the slot `ch.slots[k]` (this is the pairing of `geomAux`:
`geomAux (k+1) (pk1 :: rest) cs (childGeom k pk …)`). The geometry of a chain is unchanged by
such shifts, and so are recentering (up to the relation) and the appended child. -/

/-- A child `c'` is the child `c` with its phase shifted along the parallel direction of the
pulse `p`. -/
def ParStep (p : ℤ) (c c' : ChainChild) : Prop :=
  c'.center = c.center ∧ ∃ s : ℝ, c'.phase = c.phase + s • basisVec (parIdx p)

/-- The children `cs'` are the children `cs` with each phase shifted along the parallel direction
of the pulse `f j` of the `j`-th child. -/
def ParRel : (ℕ → ℤ) → List ChainChild → List ChainChild → Prop
  | _, [], [] => True
  | f, c :: cs, c' :: cs' => ParStep (f 0) c c' ∧ ParRel (fun j => f (j + 1)) cs cs'
  | _, _, _ => False

theorem parRel_length : ∀ (cs cs' : List ChainChild) (f : ℕ → ℤ), ParRel f cs cs' →
    cs'.length = cs.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp [ParRel])
  | _ :: _, [], _, h => absurd h (by simp [ParRel])
  | _ :: cs, _ :: cs', f, h => by
    simp [parRel_length cs cs' _ h.2]

theorem parRel_congr : ∀ (cs cs' : List ChainChild) (f g : ℕ → ℤ),
    (∀ j < cs.length, f j = g j) → ParRel f cs cs' → ParRel g cs cs'
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => absurd h (by simp [ParRel])
  | _ :: _, [], _, _, _, h => absurd h (by simp [ParRel])
  | _ :: cs, _ :: cs', f, g, hfg, h => by
    refine ⟨?_, parRel_congr cs cs' _ _ (fun j hj => hfg (j + 1) (by simpa using hj)) h.2⟩
    have := hfg 0 (by simp)
    rw [← this]; exact h.1

theorem parStep_refl (p : ℤ) (c : ChainChild) : ParStep p c c := ⟨rfl, 0, by simp⟩

theorem parRel_refl (f : ℕ → ℤ) : ∀ cs : List ChainChild, ParRel f cs cs
  | [] => trivial
  | _ :: cs => ⟨parStep_refl _ _, parRel_refl _ cs⟩

theorem parRel_snoc : ∀ (cs cs' : List ChainChild) (f : ℕ → ℤ) (c c' : ChainChild),
    cs.length = cs'.length →
    (ParRel f (cs ++ [c]) (cs' ++ [c']) ↔ ParRel f cs cs' ∧ ParStep (f cs.length) c c')
  | [], [], f, c, c', _ => by simp [ParRel]
  | [], _ :: _, _, _, _, h => absurd h (by simp)
  | _ :: _, [], _, _, _, h => absurd h (by simp)
  | a :: cs, a' :: cs', f, c, c', h => by
    have ih := parRel_snoc cs cs' (fun j => f (j + 1)) c c' (by simpa using h)
    simp only [List.cons_append, ParRel, ih, List.length_cons]
    tauto

/-- `ch'` is `ch` with each child phase shifted along the parallel direction of its pulse. -/
def ParEq (ch ch' : RealChain) : Prop :=
  ch'.baseLevel = ch.baseLevel ∧ ch'.slots = ch.slots ∧ ch'.base = ch.base ∧
    ParRel (fun j => ch.slots.getD j 0) ch.children ch'.children

theorem ParEq.refl (ch : RealChain) : ParEq ch ch :=
  ⟨rfl, rfl, rfl, parRel_refl _ _⟩

theorem ParEq.children_length {ch ch' : RealChain} (h : ParEq ch ch') :
    ch'.children.length = ch.children.length :=
  parRel_length _ _ _ h.2.2.2

theorem ParEq.wellSlotted {ch ch' : RealChain} (h : ParEq ch ch') (hl : ch.WellSlotted) :
    ch'.WellSlotted := by
  simp only [RealChain.WellSlotted] at hl ⊢
  rw [h.2.1, h.children_length]; exact hl

theorem ParEq.slot {ch ch' : RealChain} (h : ParEq ch ch') : ch'.slot = ch.slot := by
  simp only [RealChain.slot, h.2.1]

theorem geomAux_parRel (D : OCData) : ∀ (cs cs' : List ChainChild) (k : ℕ) (sl : List ℤ)
    (g : ChainGeom), ParRel (fun j => sl.getD j 0) cs cs' → D.geomAux k sl cs' g = D.geomAux k sl cs g
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => absurd h (by simp [ParRel])
  | _ :: _, [], _, _, _, h => absurd h (by simp [ParRel])
  | c :: cs, c' :: cs', k, sl, g, h => by
    match sl with
    | [] => rfl
    | [_] => rfl
    | pk :: pk1 :: rest =>
      simp only [OCData.geomAux]
      have hs : D.childGeom k pk (D.slotAnchor (k + 1) pk1) c' g =
          D.childGeom k pk (D.slotAnchor (k + 1) pk1) c g := by
        obtain ⟨⟨hc, s, hs⟩, -⟩ := h
        have hp : (fun j => (pk :: pk1 :: rest).getD j 0) 0 = pk := rfl
        rw [hp] at hs
        simp only [OCData.childGeom, hc, hs]
        refine Prod.ext (funext fun u => funext fun x => funext fun r => ?_) rfl
        simp only
        have : (D.eps k)⁻¹ • g.1 g.2.2 x r + (c.phase + s • basisVec (parIdx pk) -
            (D.eps k)⁻¹ • (g.2.1 + c.center)) = ((D.eps k)⁻¹ • g.1 g.2.2 x r + (c.phase -
            (D.eps k)⁻¹ • (g.2.1 + c.center))) + s • basisVec (parIdx pk) := by abel
        rw [this, relDisp_add_parallel]
      rw [hs]
      exact geomAux_parRel D cs cs' (k + 1) (pk1 :: rest) _ h.2

theorem ParEq.geom (D : OCData) {ch ch' : RealChain} (h : ParEq ch ch') :
    ch'.geom D = ch.geom D := by
  obtain ⟨hb, hs, hbase, hc⟩ := h
  simp only [RealChain.geom, hb, hs, hbase]
  exact geomAux_parRel D _ _ _ _ _ hc

/-- The simultaneous parallel shifts `σ j` of the phases of all children: the `j`-th child moves
by `σ j` along the parallel direction of the pulse `ch.slots[j]`. -/
def _root_.AVRegularity.RealChain.shiftChildren (ch : RealChain) (σ : ℕ → ℝ) : RealChain :=
  { ch with children := ch.children.mapIdx fun j c =>
      ⟨c.center, c.phase + σ j • basisVec (parIdx (ch.slots.getD j 0))⟩ }

/-- The parallel shift of the phase of the `k`-th child (of level `baseLevel + 1 + k`, paired with
the slot `ch.slots[k]`) by `s`. -/
def _root_.AVRegularity.RealChain.shiftChild (ch : RealChain) (k : ℕ) (s : ℝ) : RealChain :=
  ch.shiftChildren fun j => if j = k then s else 0

theorem parRel_mapIdx (σ : ℕ → ℝ) : ∀ (cs : List ChainChild) (f : ℕ → ℤ),
    ParRel f cs (cs.mapIdx fun j c => ⟨c.center, c.phase + σ j • basisVec (parIdx (f j))⟩)
  | [], _ => trivial
  | c :: cs, f => by
    rw [List.mapIdx_cons]
    exact ⟨⟨rfl, σ 0, rfl⟩, parRel_mapIdx (fun j => σ (j + 1)) cs (fun j => f (j + 1))⟩

theorem parEq_shiftChildren (ch : RealChain) (σ : ℕ → ℝ) : ParEq ch (ch.shiftChildren σ) :=
  ⟨rfl, rfl, rfl, parRel_mapIdx σ ch.children _⟩

theorem parEq_shiftChild (ch : RealChain) (k : ℕ) (s : ℝ) : ParEq ch (ch.shiftChild k s) :=
  parEq_shiftChildren ch _

/-! The operations of the generated carrier on chains respect parallel shifts of child phases:
recentering commutes with a shift (`ParEq.recenter`), appending a child commutes with a shift
of the older children (`ParEq.appendChild`), and a parallel shift of the final phase `ζ` of the
appended child is a parallel shift of the new last child (`parEq_appendChild_shift`). Here the
chain is required to be well slotted and its last slot is the slot `p` of the expression. -/

theorem getD_append_left_slots (l : List ℤ) (p' : ℤ) (j : ℕ) (hj : j < l.length) :
    (l ++ [p']).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem getD_append_last_slots (l : List ℤ) (p' : ℤ) (n : ℕ) (hl : l.length = n + 1) :
    (l ++ [p']).getD n 0 = l.getLastD 0 := by
  obtain ⟨L, a, rfl⟩ : ∃ L a, l = L ++ [a] := by
    rcases List.eq_nil_or_concat l with h | ⟨L, a, h⟩
    · simp [h] at hl
    · exact ⟨L, a, by simpa using h⟩
  have hL : L.length = n := by simpa using hl
  subst hL
  simp [List.getD_eq_getElem?_getD]

theorem getD_dropLast_slots (l : List ℤ) (j : ℕ) (hj : j + 1 < l.length) :
    l.dropLast.getD j 0 = l.getD j 0 := by
  have h1 : j < l.dropLast.length := by simp; omega
  have h2 : j < l.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    List.getElem_dropLast]

theorem ParEq.dropLastChild {ch ch' : RealChain} (h : ParEq ch ch') (hl : ch.WellSlotted)
    (cs cs' : List ChainChild) (c c' : ChainChild) (hc : ch.children = cs ++ [c])
    (hc' : ch'.children = cs' ++ [c']) :
    ParEq ch.dropLastChild ch'.dropLastChild ∧ ParStep (ch.slots.getD cs.length 0) c c' := by
  obtain ⟨hb, hs, hbase, hr⟩ := h
  rw [hc, hc'] at hr
  have hlen : cs.length = cs'.length := by
    have := parRel_length _ _ _ hr
    simp at this; omega
  rw [parRel_snoc _ _ _ _ _ hlen] at hr
  refine ⟨⟨hb, by simp [RealChain.dropLastChild, hs], hbase, ?_⟩, hr.2⟩
  simp only [RealChain.dropLastChild, hc, hc', List.dropLast_concat]
  refine parRel_congr _ _ _ _ (fun j hj => ?_) hr.1
  have hl' : ch.slots.length = cs.length + 2 := by
    have := hl; simp only [RealChain.WellSlotted, hc, List.length_append,
      List.length_singleton] at this; omega
  exact (getD_dropLast_slots ch.slots j (by omega)).symm

theorem ParEq.recenter (D : OCData) {ch ch' : RealChain} (h : ParEq ch ch')
    (hl : ch.WellSlotted) (v : Vec 2) : ParEq (ch.recenter D v) (ch'.recenter D v) := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · have hc' : ch'.children = [] := by
      have := h.children_length; rw [hc] at this; simpa using this
    rw [recenter_nil D ch hc, recenter_nil D ch' hc']
    refine ⟨h.1, h.2.1, by simp [h.2.2.1], ?_⟩
    simp only [hc, hc']; trivial
  · rw [List.concat_eq_append] at hc
    have hc' : ∃ cs' c', ch'.children = cs' ++ [c'] := by
      rcases List.eq_nil_or_concat ch'.children with h0 | ⟨cs', c', h0⟩
      · have := h.children_length; rw [h0, hc] at this; simp at this
      · exact ⟨cs', c', by simpa using h0⟩
    obtain ⟨cs', c', hc'⟩ := hc'
    obtain ⟨hd, hst⟩ := h.dropLastChild hl cs cs' c c' hc hc'
    rw [recenter_snoc D ch cs c hc v, recenter_snoc D ch' cs' c' hc' v]
    have hR : recenterShift D ch' c' v = recenterShift D ch c v := by
      have hll : ch'.lastLevel = ch.lastLevel := by
        simp [RealChain.lastLevel, h.1, h.children_length]
      simp only [recenterShift, hd.geom D, hll, h.slot, hst.1]
    have hlen : cs.length = cs'.length := by
      have := h.children_length
      rw [hc, hc'] at this; simp at this; omega
    have hll : ch'.lastLevel = ch.lastLevel := by
      simp [RealChain.lastLevel, h.1, h.children_length]
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    show ParRel (fun j => ch.slots.getD j 0) _ _
    rw [parRel_snoc _ _ _ _ _ hlen, hR, hll]
    have hr := h.2.2.2
    rw [hc, hc', parRel_snoc _ _ _ _ _ hlen] at hr
    refine ⟨hr.1, ?_, ?_⟩
    · show c'.center + _ = c.center + _
      rw [hst.1]
    · obtain ⟨-, s, hs⟩ := hst
      refine ⟨s, ?_⟩
      show c'.phase + _ = c.phase + _ + _
      rw [hs]; abel

theorem recenter_wellSlotted (D : OCData) (ch : RealChain) (hl : ch.WellSlotted)
    (v : Vec 2) : (ch.recenter D v).WellSlotted ∧ (ch.recenter D v).slot = ch.slot := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D ch hc]; exact ⟨hl, rfl⟩
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D ch cs c hc v]
    refine ⟨?_, rfl⟩
    simpa [RealChain.WellSlotted, hc] using hl

theorem ParEq.appendChild (D : OCData) {ch ch' : RealChain} (h : ParEq ch ch')
    (hl : ch.WellSlotted) (p' : ℤ) (t : ℝ) (ζ : Vec 2) :
    ParEq (ch.appendChild D p' t ζ) (ch'.appendChild D p' t ζ) := by
  have hctx : ch'.ctxLevel = ch.ctxLevel := by
    simp [RealChain.ctxLevel, RealChain.lastLevel, h.1, h.children_length]
  refine ⟨h.1, by simp [RealChain.appendChild, h.2.1], h.2.2.1, ?_⟩
  simp only [RealChain.appendChild, hctx, h.slot]
  show ParRel (fun j => (ch.slots ++ [p']).getD j 0) _ _
  rw [parRel_snoc _ _ _ _ _ h.children_length.symm]
  refine ⟨?_, parStep_refl _ _⟩
  refine parRel_congr _ _ _ _ (fun j hj => ?_) h.2.2.2
  have : ch.slots.length = ch.children.length + 1 := hl
  exact (getD_append_left_slots ch.slots p' j (by omega)).symm

theorem parEq_appendChild_shift (D : OCData) (ch : RealChain) (hl : ch.WellSlotted) (p' : ℤ)
    (t : ℝ) (ζ : Vec 2) (s : ℝ) :
    ParEq (ch.appendChild D p' t ζ) (ch.appendChild D p' t (ζ + s • basisVec (parIdx ch.slot))) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show ParRel (fun j => (ch.slots ++ [p']).getD j 0) (ch.children ++ _) (ch.children ++ _)
  rw [parRel_snoc _ _ _ _ _ rfl]
  refine ⟨parRel_refl _ _, ?_, ?_⟩
  · show _ = _
    rw [relDisp_add_parallel]
  · refine ⟨s, ?_⟩
    have : ch.slots.length = ch.children.length + 1 := hl
    rw [getD_append_last_slots _ _ _ this]
    show _ + _ + _ = _ + _ + _
    rw [relDisp_add_parallel]
    have e : ch.slots.getLastD 0 = ch.slot := rfl
    rw [e]
    abel

end AVRegularity.Providers.GenSem
end
