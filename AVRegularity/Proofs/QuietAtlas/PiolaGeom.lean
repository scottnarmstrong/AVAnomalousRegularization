-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.QuietAtlas.QuietPulse
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
@[expose] public section
open Homogenization
namespace AVRegularity.Providers.QuietAtlas

/-! **The appended child on a quiet history** (quiet matching). When the displacement of the
parent pulse vanishes between the output time `t` and the anchor `s'` of a finer slot, the
child appended at `t` has center `0` for every phase (`appendChild_geom_quiet`). On every pair of
times `u, r` between which that displacement vanishes, its offset flow is the parent flow
(`childGeom_flow_of_relDisp_zero`). So the geometric letters of the appended chain at such a time
do not read the phase (`appendChild_famJac_phase`, `appendChild_famMap_phase`,
`appendChild_famMapInv_phase`), and neither does its admissibility
(`isAdmissibleChain_appendChild_phase`): admissibility reads only centers. -/

variable (D : OCData)

/-! ### Geometric letters read only the geometry at one time -/

theorem famMap_congr {ch ch' : RealChain} {u : ℝ} (h2 : (ch.geom D).2 = (ch'.geom D).2)
    (h1 : ∀ y, (ch.geom D).1 u y (ch.geom D).2.2 = (ch'.geom D).1 u y (ch'.geom D).2.2) :
    ch.famMap D u = ch'.famMap D u := by
  funext w
  unfold RealChain.famMap
  rw [h1, h1, h2]

theorem famJac_congr {ch ch' : RealChain} {u : ℝ} (h2 : (ch.geom D).2 = (ch'.geom D).2)
    (h1 : ∀ y, (ch.geom D).1 u y (ch.geom D).2.2 = (ch'.geom D).1 u y (ch'.geom D).2.2) :
    ch.famJac D u = ch'.famJac D u := by
  unfold RealChain.famJac
  rw [funext h1, h2]

theorem famMapInv_congr {ch ch' : RealChain} {u : ℝ} (h2 : (ch.geom D).2 = (ch'.geom D).2)
    (h1 : ∀ y, (ch.geom D).1 u y (ch.geom D).2.2 = (ch'.geom D).1 u y (ch'.geom D).2.2)
    (h1' : ∀ y, (ch.geom D).1 (ch.geom D).2.2 y u = (ch'.geom D).1 (ch'.geom D).2.2 y u) :
    ch.famMapInv D u = ch'.famMapInv D u := by
  funext w
  unfold RealChain.famMapInv
  rw [h1, h1', h2]

/-! ### The appended child -/

/-- The flow of a child between two times without displacement is the parent flow. -/
theorem childGeom_flow_of_relDisp_zero (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild)
    (g : ChainGeom) {u r : ℝ} (h0 : ∀ θ, D.relDisp k pk u r θ = 0) (y : Vec 2) :
    (D.childGeom k pk s' c g).1 u y r = g.1 u (g.1 g.2.2 y r) g.2.2 := by
  simp only [OCData.childGeom, h0, smul_zero, add_zero]

/-- **The appended child has center `0`** when there is no displacement between `t` and its
anchor. -/
theorem appendChild_geom_quiet (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ)
    (z : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0) :
    (ch.appendChild D k t z).geom D =
      D.childGeom ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) ⟨0, z⟩ (ch.geom D) := by
  rw [GenSem.appendChild_geom D ch hl k t z, h0, smul_zero, add_zero]

/-- The point and the anchor of the appended chain do not read the phase. -/
theorem appendChild_geom_snd_phase (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ)
    (z z' : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0) :
    ((ch.appendChild D k t z).geom D).2 = ((ch.appendChild D k t z').geom D).2 := by
  rw [appendChild_geom_quiet D ch hl k t z h0, appendChild_geom_quiet D ch hl k t z' h0]
  rfl

/-- The flow of the appended chain between two times without displacement does not read the
phase. -/
theorem appendChild_geom_fst_phase (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ)
    (z z' : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0)
    {u r : ℝ} (hur : ∀ θ, D.relDisp ch.ctxLevel ch.slot u r θ = 0) (y : Vec 2) :
    ((ch.appendChild D k t z).geom D).1 u y r = ((ch.appendChild D k t z').geom D).1 u y r := by
  rw [appendChild_geom_quiet D ch hl k t z h0, appendChild_geom_quiet D ch hl k t z' h0,
    childGeom_flow_of_relDisp_zero D _ _ _ _ _ hur, childGeom_flow_of_relDisp_zero D _ _ _ _ _ hur]

theorem appendChild_anchor (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ) (z : Vec 2) :
    ((ch.appendChild D k t z).geom D).2.2 = D.slotAnchor (ch.ctxLevel + 1) k := by
  rw [GenSem.appendChild_geom D ch hl k t z]
  rfl

/-- **The Jacobian of the appended chain at a time `u` without displacement from its anchor does
not read the phase.** -/
theorem appendChild_famJac_phase (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ)
    (z z' : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0)
    {u : ℝ} (hu : ∀ θ, D.relDisp ch.ctxLevel ch.slot u (D.slotAnchor (ch.ctxLevel + 1) k) θ = 0) :
    (ch.appendChild D k t z).famJac D u = (ch.appendChild D k t z').famJac D u := by
  refine famJac_congr D (appendChild_geom_snd_phase D ch hl k t z z' h0) fun y => ?_
  rw [appendChild_anchor D ch hl k t z, appendChild_anchor D ch hl k t z']
  exact appendChild_geom_fst_phase D ch hl k t z z' h0 hu y

theorem appendChild_famMap_phase (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ)
    (z z' : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0)
    {u : ℝ} (hu : ∀ θ, D.relDisp ch.ctxLevel ch.slot u (D.slotAnchor (ch.ctxLevel + 1) k) θ = 0) :
    (ch.appendChild D k t z).famMap D u = (ch.appendChild D k t z').famMap D u := by
  refine famMap_congr D (appendChild_geom_snd_phase D ch hl k t z z' h0) fun y => ?_
  rw [appendChild_anchor D ch hl k t z, appendChild_anchor D ch hl k t z']
  exact appendChild_geom_fst_phase D ch hl k t z z' h0 hu y

theorem appendChild_famMapInv_phase (ch : RealChain) (hl : ch.WellSlotted) (k : ℤ) (t : ℝ)
    (z z' : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0)
    {u : ℝ} (hu : ∀ θ, D.relDisp ch.ctxLevel ch.slot u (D.slotAnchor (ch.ctxLevel + 1) k) θ = 0)
    (hu' : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) u θ = 0) :
    (ch.appendChild D k t z).famMapInv D u = (ch.appendChild D k t z').famMapInv D u := by
  refine famMapInv_congr D (appendChild_geom_snd_phase D ch hl k t z z' h0) (fun y => ?_)
    fun y => ?_
  · rw [appendChild_anchor D ch hl k t z, appendChild_anchor D ch hl k t z']
    exact appendChild_geom_fst_phase D ch hl k t z z' h0 hu y
  · rw [appendChild_anchor D ch hl k t z, appendChild_anchor D ch hl k t z']
    exact appendChild_geom_fst_phase D ch hl k t z z' h0 hu' y

/-! ### Admissibility reads only centers -/

theorem isCarrierChain_congr {b : ℝ} {j₀ i : ℕ} {p : ℤ} {mres : ℝ} {ch ch' : RealChain}
    (hb : ch.baseLevel = ch'.baseLevel) (hs : ch.slots = ch'.slots)
    (hc : ch.children.map ChainChild.center = ch'.children.map ChainChild.center) :
    IsCarrierChain D b j₀ i p mres ch → IsCarrierChain D b j₀ i p mres ch' := by
  have hlen : ch.children.length = ch'.children.length := by
    simpa using congrArg List.length hc
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, hb ▸ h2, hs ▸ hlen ▸ h3, ?_, hs ▸ h5, ?_, ?_⟩
  · simpa only [RealChain.ctxLevel, RealChain.lastLevel, hb, hlen] using h1
  · simpa only [RealChain.slot, hs] using h4
  · intro k hk
    have hk' : k + 1 < ch.slots.length := by rw [hs]; exact hk
    have := h6 k hk'
    simp only [hs, hb] at this
    exact this
  · intro k hk
    have hk' : k < ch.children.length := by rw [hlen]; exact hk
    have hck : (ch'.children[k]).center = (ch.children[k]).center := by
      have e := congrArg (fun l => l[k]?) hc
      simp only [List.getElem?_map, List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk,
        Option.map_some, Option.some.injEq] at e
      exact e.symm
    rw [hck, ← hb]
    exact h7 k hk'

/-- The appended chain with center `0`, as a record. -/
theorem appendChild_eq_quiet (ch : RealChain) (k : ℤ) (t : ℝ) (z : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0) :
    ch.appendChild D k t z =
      { ch with slots := ch.slots ++ [k], children := ch.children ++ [⟨0, z⟩] } := by
  simp only [RealChain.appendChild, h0, smul_zero, add_zero]

/-- **Admissibility of the appended chain does not read the phase.** -/
theorem isAdmissibleChain_appendChild_phase {b : ℝ} {j₀ i : ℕ} {p : ℤ} (ch : RealChain)
    (k : ℤ) (t : ℝ) (z z' : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0) :
    IsAdmissibleChain D b j₀ i p (ch.appendChild D k t z) ↔
      IsAdmissibleChain D b j₀ i p (ch.appendChild D k t z') := by
  rw [appendChild_eq_quiet D ch k t z h0, appendChild_eq_quiet D ch k t z' h0]
  exact ⟨isCarrierChain_congr D rfl rfl (by simp), isCarrierChain_congr D rfl rfl (by simp)⟩

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.QuietAtlas

/-! **The quiet-chart identities of the finer outputs from the carried invariant** (quiet
matching). On a history-quiet set, the children appended at an active finer slot

* with two phases (QC1, `quietPhaseBlind_of_finerHistory`), and
* in the two renewal descriptions of an overlap (QC2, `quietReanchors_of_finerHistory`)

are admissible and have the same history geometry over the availability interval of the finer
slot. There the parent pulse displaces nothing, so the child flow is the parent flow, and the two
native chains related by the renewal transition carry the same physical flow and point (flow
group law). So `FinerHistoryInvariant` gives both identities. The instantiations need to supply
only the finer-operator invariant. -/

/-- The group law of a flow of the data. -/
theorem flowOf_group (D : OCData) (k : ℕ) (x : Vec 2) (s r u : ℝ) :
    D.flowOf k u (D.flowOf k r x s) r = D.flowOf k u x s :=
  AVenhance.Infra.Flow.flow_group_law _ (D.hΦ k).vel_lipschitz
    (AVenhance.flow_isFlow _ (D.hΦ k).vel_continuous (D.hΦ k).vel_lipschitz) x s r u

variable {D : OCData} {b : ℝ} {j₀ : ℕ}

/-- **The appended chain at an active finer slot is admissible** when its child has center
`0`. -/
theorem isAdmissibleChain_appendChild (hb : 0 < b) (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ}
    {ch : RealChain} (hch : IsAdmissibleChain D b j₀ i p ch) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hkt : ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0) (htp : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    (z : Vec 2)
    (h0 : ∀ θ, D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) k) t θ = 0) :
    IsAdmissibleChain D b j₀ (i + 1) k (ch.appendChild D k t z) := by
  rw [appendChild_eq_quiet D ch k t z h0]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hch
  have hctx : ch.baseLevel + ch.children.length + 1 = i := h1
  have hslot : ch.slots.getLastD 0 = p := h4
  refine ⟨?_, h2, ?_, ?_, ?_, ?_, ?_⟩
  · change ch.baseLevel + (ch.children ++ [(⟨0, z⟩ : ChainChild)]).length + 1 = i + 1
    rw [List.length_append]
    simp only [List.length_singleton]
    omega
  · simp only [List.length_append, List.length_singleton]
    rw [h3]
  · change (ch.slots ++ [k]).getLastD 0 = k
    simp
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h5 x hx
    · rw [List.mem_singleton.mp hx]; exact hk
  · intro n hn
    simp only [List.length_append, List.length_singleton] at hn
    by_cases hlt : n + 1 < ch.slots.length
    · rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
      exact h6 n hlt
    · have hn1 : n + 1 = ch.slots.length := by omega
      have hne : ch.slots ≠ [] := by
        intro h; rw [h] at hn1; simp at hn1
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
      simp only [hn1, Nat.sub_self, List.getElem_singleton]
      have hlast : ch.slots[n]'(by omega) = p := by
        rw [← hslot, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        rw [show ch.slots.length - 1 = n by omega,
          List.getElem?_eq_getElem (show n < ch.slots.length by omega)]
        rfl
      rw [hlast]
      have hlev : ch.baseLevel + 1 + n = i := by omega
      rw [hlev]
      exact ⟨t, hkt, htp⟩
  · intro n hn
    simp only [List.length_append, List.length_singleton] at hn
    by_cases hlt : n < ch.children.length
    · rw [List.getElem_append_left hlt]
      exact h7 n hlt
    · rw [List.getElem_append_right (by omega)]
      simp only [show n - ch.children.length = 0 by omega, List.getElem_singleton]
      have hε : 0 < D.eps (ch.baseLevel + 1 + n) := Construction.Stream.ocEpsilon_pos hΛ
      simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero]
      positivity

/-- The native chain recentered: the base label is moved. -/
theorem nativeChain_recenter (i : ℕ) (p : ℤ) (h : Vec 2) :
    (nativeChain i p).recenter D h = ⟨i - 1, [p], 0 + h, []⟩ := rfl

theorem isAdmissibleChain_nativeChain_recenter {i : ℕ} (hi : 1 ≤ i) (hj : j₀ ≤ i) (p : OddSlot)
    (h : Vec 2) : IsAdmissibleChain D b j₀ i p.1 ((nativeChain i p.1).recenter D h) := by
  rw [nativeChain_recenter]
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · change i - 1 + 0 + 1 = i
    omega
  · change j₀ ≤ i - 1 + 1
    omega
  · intro x hx
    rw [List.mem_singleton.mp hx]
    exact p.2
  · intro n hn
    exact absurd hn (by simp)
  · intro n hn
    exact absurd hn (by simp)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {Dm : ℕ}

/-- **QC1 from the carried invariant.** -/
theorem quietPhaseBlind_of_finerHistory (hb : 0 < b) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ)
    (hU : IsHistoryQuiet D Mtop G.level U) (hF : FinerHistoryInvariant G P Mtop) :
    QuietPhaseBlind G P U := by
  intro v u γ p ch t ht htp k hk hkt n hn z z' f
  obtain ⟨h1, -, h3, h4, -, -, -⟩ := ch.2
  have hl : ch.1.WellSlotted := h3
  have hctx : ch.1.ctxLevel = G.level := h1
  have hslot : ch.1.slot = p.1 := h4
  have hz : ∀ u r, u ∈ availInterval D Mtop (G.level + 1) k →
      r ∈ availInterval D Mtop (G.level + 1) k →
      ∀ θ, D.relDisp ch.1.ctxLevel ch.1.slot u r θ = 0 := by
    intro u r hu hr θ
    rw [hctx, hslot]
    exact relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt p.2 hu hr θ
  have hsk : D.slotAnchor (ch.1.ctxLevel + 1) k ∈ availInterval D Mtop (G.level + 1) k := by
    rw [hctx]
    exact slotAnchor_mem_availInterval D Mtop (G.level + 1) k
  have htk : t ∈ availInterval D Mtop (G.level + 1) k := mem_availInterval_of_ocCutoff D hΛ hkt
  have h0 : ∀ θ, D.relDisp ch.1.ctxLevel ch.1.slot (D.slotAnchor (ch.1.ctxLevel + 1) k) t θ = 0 :=
    hz _ _ hsk htk
  let A : StageCtx D b j₀ (G.level + 1) ⟨k, hk⟩ :=
    ⟨_, isAdmissibleChain_appendChild hb hΛ ch.2 hk hkt htp z h0⟩
  let A' : StageCtx D b j₀ (G.level + 1) ⟨k, hk⟩ :=
    ⟨_, isAdmissibleChain_appendChild hb hΛ ch.2 hk hkt htp z' h0⟩
  have hsame : SameHistoryGeometry D Mtop (G.level + 1) k A.1 A'.1 := by
    intro s hs
    have hs0 := hz _ _ hs hsk
    refine ⟨appendChild_famMap_phase D ch.1 hl k t z z' h0 hs0, ?_⟩
    have h2 := appendChild_geom_snd_phase D ch.1 hl k t z z' h0
    change ((ch.1.appendChild D k t z).geom D).1 s ((ch.1.appendChild D k t z).geom D).2.1
        ((ch.1.appendChild D k t z).geom D).2.2 =
      ((ch.1.appendChild D k t z').geom D).1 s ((ch.1.appendChild D k t z').geom D).2.1
        ((ch.1.appendChild D k t z').geom D).2.2
    rw [congrArg Prod.fst h2, congrArg Prod.snd h2, appendChild_anchor D ch.1 hl k t z']
    exact appendChild_geom_fst_phase D ch.1 hl k t z z' h0 hs0 _
  exact hF v u γ n hn ⟨k, hk⟩ A A' hsame t
    (GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hkt) f

/-- **QC2 from the carried invariant.** -/
theorem quietReanchors_of_finerHistory (hb : 0 < b) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hU : IsHistoryQuiet D Mtop G.level U)
    (hF : FinerHistoryInvariant G P Mtop) : QuietReanchors G P U := by
  intro v u γ p q _ t ht htp htq k hk hkt n hn Y z f
  set Yp := renewalTransition D G.level p q Y
  set chp := (nativeChain G.level p.1).recenter D Yp
  set chq := (nativeChain G.level q.1).recenter D Y
  have hap := isAdmissibleChain_nativeChain_recenter (D := D) (b := b) hi hj p Yp
  have haq := isAdmissibleChain_nativeChain_recenter (D := D) (b := b) hi hj q Y
  have hlp : chp.WellSlotted := hap.2.2.1
  have hlq : chq.WellSlotted := haq.2.2.1
  have hctxp : chp.ctxLevel = G.level := hap.1
  have hctxq : chq.ctxLevel = G.level := haq.1
  have hslotp : chp.slot = p.1 := hap.2.2.2.1
  have hslotq : chq.slot = q.1 := haq.2.2.2.1
  have hzr : ∀ (c : OddSlot) u r, u ∈ availInterval D Mtop (G.level + 1) k →
      r ∈ availInterval D Mtop (G.level + 1) k →
      ∀ θ, D.relDisp G.level c.1 u r θ = 0 :=
    fun c u r hu hr θ => relDisp_eq_zero_of_historyQuiet D hΛ hζ hU ht hkt c.2 hu hr θ
  have hsk : D.slotAnchor (G.level + 1) k ∈ availInterval D Mtop (G.level + 1) k :=
    slotAnchor_mem_availInterval D Mtop (G.level + 1) k
  have htk : t ∈ availInterval D Mtop (G.level + 1) k := mem_availInterval_of_ocCutoff D hΛ hkt
  have h0p : ∀ θ, D.relDisp chp.ctxLevel chp.slot (D.slotAnchor (chp.ctxLevel + 1) k) t θ = 0 := by
    rw [hctxp, hslotp]; exact hzr p _ _ hsk htk
  have h0q : ∀ θ, D.relDisp chq.ctxLevel chq.slot (D.slotAnchor (chq.ctxLevel + 1) k) t θ = 0 := by
    rw [hctxq, hslotq]; exact hzr q _ _ hsk htk
  let A : StageCtx D b j₀ (G.level + 1) ⟨k, hk⟩ :=
    ⟨_, isAdmissibleChain_appendChild hb hΛ hap hk hkt htp z h0p⟩
  let A' : StageCtx D b j₀ (G.level + 1) ⟨k, hk⟩ :=
    ⟨_, isAdmissibleChain_appendChild hb hΛ haq hk hkt htq z h0q⟩
  -- the two appended geometries
  have hgp := appendChild_geom_quiet D chp hlp k t z h0p
  have hgq := appendChild_geom_quiet D chq hlq k t z h0q
  have hlev : G.level - 1 + 1 = G.level := by omega
  have hgeomp : chp.geom D = (D.flowOf (G.level - 1), 0 + Yp, D.slotAnchor G.level p.1) := by
    change (D.flowOf (G.level - 1), 0 + Yp, D.slotAnchor (G.level - 1 + 1) p.1) = _
    rw [hlev]
  have hgeomq : chq.geom D = (D.flowOf (G.level - 1), 0 + Y, D.slotAnchor G.level q.1) := by
    change (D.flowOf (G.level - 1), 0 + Y, D.slotAnchor (G.level - 1 + 1) q.1) = _
    rw [hlev]
  rw [hgeomp, hctxp, hslotp] at hgp
  rw [hgeomq, hctxq, hslotq] at hgq
  have h2 : ((chp.appendChild D k t z).geom D).2 = ((chq.appendChild D k t z).geom D).2 := by
    rw [hgp, hgq]
    simp only [OCData.childGeom, zero_add, add_zero, Yp, renewalTransition]
    rw [flowOf_group]
  have h1 : ∀ s, s ∈ availInterval D Mtop (G.level + 1) k → ∀ y,
      ((chp.appendChild D k t z).geom D).1 s y (D.slotAnchor (G.level + 1) k) =
        ((chq.appendChild D k t z).geom D).1 s y (D.slotAnchor (G.level + 1) k) := by
    intro s hs y
    rw [hgp, hgq, childGeom_flow_of_relDisp_zero D _ _ _ _ _ (hzr p _ _ hs hsk),
      childGeom_flow_of_relDisp_zero D _ _ _ _ _ (hzr q _ _ hs hsk)]
    simp only
    rw [flowOf_group, flowOf_group]
  have hanc : ((chp.appendChild D k t z).geom D).2.2 = D.slotAnchor (G.level + 1) k := by
    rw [appendChild_anchor D chp hlp k t z, hctxp]
  have hancq : ((chq.appendChild D k t z).geom D).2.2 = D.slotAnchor (G.level + 1) k := by
    rw [appendChild_anchor D chq hlq k t z, hctxq]
  have hsame : SameHistoryGeometry D Mtop (G.level + 1) k A.1 A'.1 := by
    intro s hs
    refine ⟨famMap_congr D h2 fun y => ?_, ?_⟩
    · rw [hanc, hancq]; exact h1 s hs y
    · change ((chp.appendChild D k t z).geom D).1 s ((chp.appendChild D k t z).geom D).2.1
          ((chp.appendChild D k t z).geom D).2.2 =
        ((chq.appendChild D k t z).geom D).1 s ((chq.appendChild D k t z).geom D).2.1
          ((chq.appendChild D k t z).geom D).2.2
      rw [congrArg Prod.fst h2, hanc, hancq]
      exact h1 s hs _
  exact hF v u γ n hn ⟨k, hk⟩ A A' hsame t
    (GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hkt) f

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Providers.QuietAtlas

/-! **The history geometry of chains** (the carried quiet invariant). `HistEq g g' I`: the two
offset flows agree, from their common anchor, at every time of `I`, once the labels are shifted
by the difference of the base points. For chains over the same slot this is
`SameHistoryGeometry` (`histEq_iff_sameHistory`). It is preserved by recentering
(`histEq_recenter`, the recentered family is the same flow at a shifted point). It is inherited
by the appended children on every subset of `I` containing their anchor (`histEq_childGeom`):
the child's offset from its parent is the same once the labels are shifted, by the inverse law.
Equal history geometry at a time gives the same Jacobian there (`famJac_eq_of_histEq`). The
anchor of a chain is the anchor of its slot (`geom_anchor`). Availability intervals are nested
(`availInterval_child_subset`). -/

/-- Two geometries agree on the times `I` up to the shift of the label. -/
def HistEq (g g' : ChainGeom) (I : Set ℝ) : Prop :=
  g.2.2 = g'.2.2 ∧ ∀ s ∈ I, ∀ h : Vec 2, g.1 s (g.2.1 + h) g.2.2 = g'.1 s (g'.2.1 + h) g'.2.2

theorem HistEq.mono {g g' : ChainGeom} {I J : Set ℝ} (h : HistEq g g' I) (hJ : J ⊆ I) :
    HistEq g g' J :=
  ⟨h.1, fun s hs => h.2 s (hJ hs)⟩

variable (D : OCData)

/-- The anchor of the last family of a chain. -/
theorem geomAux_anchor : ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) (g : ChainGeom),
    sl.length = cs.length + 1 → g.2.2 = D.slotAnchor k (sl.headD 0) →
    (D.geomAux k sl cs g).2.2 = D.slotAnchor (k + cs.length) (sl.getLastD 0)
  | [], k, sl, g, hl, hg => by
    match sl, hl with
    | [pk], _ => simpa [OCData.geomAux] using hg
  | c :: cs, k, sl, g, hl, _ => by
    match sl, hl with
    | pk :: pk1 :: rest, hl =>
      have hl' : (pk1 :: rest).length = cs.length + 1 := by simpa using hl
      rw [show D.geomAux k (pk :: pk1 :: rest) (c :: cs) g =
        D.geomAux (k + 1) (pk1 :: rest) cs (D.childGeom k pk (D.slotAnchor (k + 1) pk1) c g)
        from rfl, geomAux_anchor cs (k + 1) (pk1 :: rest) _ hl' rfl]
      simp only [List.length_cons, List.getLastD_cons]
      congr 1
      omega

theorem geom_anchor (ch : RealChain) (hl : ch.WellSlotted) :
    (ch.geom D).2.2 = D.slotAnchor ch.ctxLevel ch.slot := by
  unfold RealChain.geom
  rw [geomAux_anchor D ch.children _ ch.slots _ hl rfl]
  simp only [RealChain.ctxLevel, RealChain.lastLevel, RealChain.slot]
  congr 1
  omega

/-- For chains with a common anchor, `SameHistoryGeometry` is `HistEq`. -/
theorem histEq_iff_sameHistory {Mtop m : ℕ} {p : ℤ} (ch ch' : RealChain)
    (hanc : (ch.geom D).2.2 = (ch'.geom D).2.2) :
    HistEq (ch.geom D) (ch'.geom D) (availInterval D Mtop m p) ↔
      SameHistoryGeometry D Mtop m p ch ch' := by
  constructor
  · intro h s hs
    have h0 : (ch.geom D).1 s (ch.geom D).2.1 (ch.geom D).2.2 =
        (ch'.geom D).1 s (ch'.geom D).2.1 (ch'.geom D).2.2 := by
      simpa only [add_zero] using h.2 s hs 0
    refine ⟨funext fun w => ?_, h0⟩
    simp only [RealChain.famMap]
    rw [h.2 s hs w, h0]
  · intro h
    refine ⟨hanc, fun s hs w => ?_⟩
    obtain ⟨h1, h2⟩ := h s hs
    have h3 := congrFun h1 w
    unfold RealChain.famMap at h3
    rw [h2] at h3
    exact sub_left_inj.mp h3

/-- Recentering preserves the history geometry. -/
theorem histEq_recenter (hζ : IsFastProfile D.ζ) {ch ch' : RealChain} (hl : ch.WellSlotted)
    (hl' : ch'.WellSlotted) {I : Set ℝ} (h : HistEq (ch.geom D) (ch'.geom D) I) (H : Vec 2) :
    HistEq ((ch.recenter D H).geom D) ((ch'.recenter D H).geom D) I := by
  rw [GenSem.geom_recenter D hζ ch hl H, GenSem.geom_recenter D hζ ch' hl' H]
  refine ⟨h.1, fun s hs w => ?_⟩
  simp only [add_assoc]
  exact h.2 s hs (H + w)

/-- **Appended children inherit the history geometry.** -/
theorem histEq_childGeom {g g' : ChainGeom} (hinv : ChainGeometry.InvLaw g)
    (hinv' : ChainGeometry.InvLaw g') {I J : Set ℝ} (hgg : HistEq g g' I) (k : ℕ) (pk : ℤ)
    {s' : ℝ} (c : ChainChild) (hs' : s' ∈ I) (hJ : J ⊆ I) :
    HistEq (D.childGeom k pk s' c g) (D.childGeom k pk s' c g') J := by
  obtain ⟨ha, hF⟩ := hgg
  refine ⟨rfl, fun u hu w => ?_⟩
  simp only [OCData.childGeom]
  -- the child's point
  have hP : g.1 s' (g.2.1 + c.center) g.2.2 = g'.1 s' (g'.2.1 + c.center) g'.2.2 :=
    hF s' hs' c.center
  rw [← hP]
  set P := g.1 s' (g.2.1 + c.center) g.2.2
  -- the offset of the child label from the parent label
  have hw : g.1 g.2.2 (P + w) s' - g.2.1 = g'.1 g'.2.2 (P + w) s' - g'.2.1 := by
    set v := g'.1 g'.2.2 (P + w) s' - g'.2.1
    have h1 : g'.1 s' (g'.2.1 + v) g'.2.2 = P + w := by
      simp only [v, add_sub_cancel]
      exact hinv' s' g'.2.2 (P + w)
    rw [← hF s' hs' v] at h1
    rw [← h1, hinv g.2.2 s' (g.2.1 + v)]
    abel
  set v := g.1 g.2.2 (P + w) s' - g.2.1
  have hx : g.1 g.2.2 (P + w) s' = g.2.1 + v := by simp only [v]; abel
  have hx' : g'.1 g'.2.2 (P + w) s' = g'.2.1 + v := by rw [hw]; abel
  rw [hx, hx']
  have harg : ∀ x : Vec 2, (D.eps k)⁻¹ • (x + v) + (c.phase - (D.eps k)⁻¹ • (x + c.center)) =
      (D.eps k)⁻¹ • v + (c.phase - (D.eps k)⁻¹ • c.center) := fun x => by
    simp only [smul_add]
    abel
  rw [harg g.2.1, harg g'.2.1, add_assoc, add_assoc]
  exact hF u (hJ hu) _

/-- Equal history geometry at a time gives the same Jacobian there. -/
theorem famJac_eq_of_histEq {ch ch' : RealChain} {I : Set ℝ}
    (h : HistEq (ch.geom D) (ch'.geom D) I) {u : ℝ} (hu : u ∈ I) :
    ch.famJac D u = ch'.famJac D u := by
  unfold RealChain.famJac jacMatrix
  ext i j
  simp only [Matrix.of_apply]
  have hf : (fun y => (ch.geom D).1 u ((ch.geom D).2.1 + y) (ch.geom D).2.2) =
      fun y => (ch'.geom D).1 u ((ch'.geom D).2.1 + y) (ch'.geom D).2.2 := funext (h.2 u hu)
  have e1 := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => (ch.geom D).1 u y (ch.geom D).2.2)
    (x := (0 : Vec 2)) (ch.geom D).2.1
  have e2 := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => (ch'.geom D).1 u y (ch'.geom D).2.2)
    (x := (0 : Vec 2)) (ch'.geom D).2.1
  simp only [add_zero] at e1 e2
  rw [← e1, ← e2, hf]

/-- The availability interval of a scheduled finer slot lies in the one of its slot. -/
theorem availInterval_child_subset {Mtop m : ℕ} (hm : m < Mtop) {p k : ℤ} (hk : Odd k)
    (hsch : IsScheduledIn D m k p) :
    availInterval D Mtop (m + 1) k ⊆ availInterval D Mtop m p := by
  unfold availInterval
  obtain ⟨f, hf⟩ : ∃ f, Mtop - m = f + 1 := ⟨Mtop - m - 1, by omega⟩
  rw [hf, show Mtop - (m + 1) = f by omega]
  intro x hx
  exact mem_intervalHull (Or.inr (Or.inr (Set.mem_biUnion (x := k) ⟨hk, hsch⟩ hx)))

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.QuietAtlas

/-! **The chart changes of the Piola leaf** (quiet matching).
* `hder_of_inverse`: for a smooth label map `ψ` with inverse `χ`, the fields `∑_b K_{bj} ∂_b`
  of `K = (Dψ)⁻¹` read `f ∘ ψ` as `∂_j f ∘ ψ` (the hypothesis of `transitionT_comp`).
* `chartInvJacobian_translate`, `chartInvJacobian_comp`: the inverse Jacobian of a translated
  map, and of a composition.
* `childTransition_inv_native`: on a quiet history, the transfer Jacobian of a native chain over
  the slot `p` at the base label `X` is the inverse Jacobian of the label change
  `φ_p = X_{m-1}(s_k, ·, s_p)` to the anchor of the finer slot. The appended child has center `0`
  and carries the parent flow, and `F_t = F♮_t · Dφ_p` by the group law. -/

open CycleComparison.Reconstruction

/-- **The fields of `(Dψ)⁻¹` read `f ∘ ψ` as `∂ f ∘ ψ`.** -/
theorem hder_of_inverse {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (f : Vec 2 → ℝ) (x : Vec 2) (j : Fin 2) (hf : DifferentiableAt ℝ f (ψ x)) :
    ∑ b : Fin 2, chartInvJacobian ψ x b j * fderiv ℝ (f ∘ ψ) x (basisVec b) =
      fderiv ℝ f (ψ x) (basisVec j) := by
  have hid : (fderiv ℝ ψ x).comp (fderiv ℝ χ (ψ x)) = ContinuousLinearMap.id ℝ (Vec 2) := by
    have h1 : HasFDerivAt (ψ ∘ χ) ((fderiv ℝ ψ (χ (ψ x))).comp (fderiv ℝ χ (ψ x))) (ψ x) :=
      (hψ (χ (ψ x))).hasFDerivAt.comp (ψ x) (hχ (ψ x)).hasFDerivAt
    rw [show ψ ∘ χ = id from funext hψχ] at h1
    have h2 := h1.unique (hasFDerivAt_id (ψ x))
    rwa [hχψ x] at h2
  simp only [chartInvJacobian_apply_of_inverse hχ hψ hψχ hχψ, fderiv_comp x hf (hψ x),
    ContinuousLinearMap.comp_apply]
  have hsum : ∑ b : Fin 2, fderiv ℝ χ (ψ x) (basisVec j) b *
      fderiv ℝ f (ψ x) (fderiv ℝ ψ x (basisVec b)) =
      fderiv ℝ f (ψ x) (fderiv ℝ ψ x (∑ b : Fin 2,
        fderiv ℝ χ (ψ x) (basisVec j) b • basisVec b)) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hsum, ← AVRegularity.ChartTransport.vec2_eq_sum_basisVec]
  have h3 := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec j)) hid
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h3
  rw [h3]

/-- The inverse Jacobian of a translated map. -/
theorem chartInvJacobian_translate (Υ : Vec 2 → Vec 2) (Y c h : Vec 2) :
    chartInvJacobian (fun h => Υ (Y + h) - c) h = chartInvJacobian Υ (Y + h) := by
  unfold chartInvJacobian chartJacobian
  congr 1
  ext i a
  simp only [Matrix.of_apply, fderiv_sub_const, fderiv_comp_add_left]

/-- The inverse Jacobian of a composition. -/
theorem chartInvJacobian_comp {φ Υ : Vec 2 → Vec 2} (x : Vec 2)
    (hφ : DifferentiableAt ℝ φ (Υ x)) (hΥ : DifferentiableAt ℝ Υ x) :
    chartInvJacobian (φ ∘ Υ) x = chartInvJacobian Υ x * chartInvJacobian φ (Υ x) := by
  unfold chartInvJacobian
  rw [CycleComparison.Reconstruction.chartJacobian_eq_jacMatrix,
    CycleComparison.Reconstruction.chartJacobian_eq_jacMatrix,
    CycleComparison.Reconstruction.chartJacobian_eq_jacMatrix,
    CycleReference.jacMatrix_comp x hφ hΥ, Matrix.mul_inv_rev]

variable (D : OCData)

theorem flowOf_contDiff (k : ℕ) (t s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => D.flowOf k t y s) :=
  CycleReference.streamFlow_spatial_smooth (D.hΦ k) t s

theorem flowOf_det (k : ℕ) (t s : ℝ) (y : Vec 2) :
    (jacMatrix (fun x => D.flowOf k t x s) y).det = 1 :=
  CycleReference.streamFlow_jacMatrix_det_one (D.hΦ k) t s y

/-- **The transfer Jacobian of a native chain on a quiet history.** -/
theorem childTransition_inv_native {m : ℕ} (hm : 1 ≤ m) {p k : ℤ} {t : ℝ} (X ζ : Vec 2)
    (h0 : ∀ θ, D.relDisp m p (D.slotAnchor (m + 1) k) t θ = 0)
    (h1 : ∀ θ, D.relDisp m p t (D.slotAnchor (m + 1) k) θ = 0) :
    (childTransition D k t ⟨m - 1, [p], X, []⟩ ζ)⁻¹ =
      chartInvJacobian (fun y => D.flowOf (m - 1) (D.slotAnchor (m + 1) k) y (D.slotAnchor m p))
        X := by
  set c : RealChain := ⟨m - 1, [p], X, []⟩ with hc
  have hl : c.WellSlotted := rfl
  have hctx : c.ctxLevel = m := by
    show m - 1 + 0 + 1 = m
    omega
  have hslot : c.slot = p := rfl
  have hgeom : c.geom D = (D.flowOf (m - 1), X, D.slotAnchor m p) := by
    show (D.flowOf (m - 1), X, D.slotAnchor (m - 1 + 1) p) = _
    rw [Nat.sub_add_cancel hm]
  have h0' : ∀ θ, D.relDisp c.ctxLevel c.slot (D.slotAnchor (c.ctxLevel + 1) k) t θ = 0 := by
    rw [hctx, hslot]
    exact h0
  have hg := appendChild_geom_quiet D c hl k t ζ h0'
  rw [hgeom, hctx, hslot] at hg
  have hF : c.famJac D t = jacMatrix (fun y => D.flowOf (m - 1) t y (D.slotAnchor m p)) X := by
    unfold RealChain.famJac
    rw [hgeom]
  have hFa : (c.appendChild D k t ζ).famJac D t =
      jacMatrix (fun y => D.flowOf (m - 1) t y (D.slotAnchor (m + 1) k))
        (D.flowOf (m - 1) (D.slotAnchor (m + 1) k) X (D.slotAnchor m p)) := by
    unfold RealChain.famJac
    rw [hg]
    have hfun : (fun y => (D.childGeom m p (D.slotAnchor (m + 1) k) ⟨0, ζ⟩
        (D.flowOf (m - 1), X, D.slotAnchor m p)).1 t y
          (D.childGeom m p (D.slotAnchor (m + 1) k) ⟨0, ζ⟩
            (D.flowOf (m - 1), X, D.slotAnchor m p)).2.2) =
        fun y => D.flowOf (m - 1) t y (D.slotAnchor (m + 1) k) := by
      funext y
      rw [show (D.childGeom m p (D.slotAnchor (m + 1) k) ⟨0, ζ⟩
          (D.flowOf (m - 1), X, D.slotAnchor m p)).2.2 = D.slotAnchor (m + 1) k from rfl,
        childGeom_flow_of_relDisp_zero D _ _ _ _ _ h1]
      exact flowOf_group D _ _ _ _ _
    rw [hfun]
    simp only [OCData.childGeom, add_zero]
  have hcomp : (fun y => D.flowOf (m - 1) t y (D.slotAnchor m p)) =
      (fun y => D.flowOf (m - 1) t y (D.slotAnchor (m + 1) k)) ∘
        (fun y => D.flowOf (m - 1) (D.slotAnchor (m + 1) k) y (D.slotAnchor m p)) := by
    funext y
    exact (flowOf_group D _ _ _ _ _).symm
  have hJ := CycleReference.jacMatrix_comp (f := fun y => D.flowOf (m - 1) t y (D.slotAnchor (m + 1) k))
    (g := fun y => D.flowOf (m - 1) (D.slotAnchor (m + 1) k) y (D.slotAnchor m p)) X
    ((flowOf_contDiff D _ _ _).differentiable (by simp) _)
    ((flowOf_contDiff D _ _ _).differentiable (by simp) _)
  have hunit : IsUnit (jacMatrix (fun y => D.flowOf (m - 1) t y (D.slotAnchor (m + 1) k))
      (D.flowOf (m - 1) (D.slotAnchor (m + 1) k) X (D.slotAnchor m p))).det := by
    rw [flowOf_det]
    exact isUnit_one
  unfold childTransition
  rw [hF, hFa, hcomp, hJ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rfl

end AVRegularity.Providers.QuietAtlas
end
end
